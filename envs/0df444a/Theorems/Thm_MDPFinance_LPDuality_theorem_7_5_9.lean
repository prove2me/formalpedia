-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_5_9
-- name    : MDPFinance.LPDuality.theorem_7_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:56:36.278756+00:00
-- url     : https://prove2.me/theorems/444f8ac9-0968-4735-afe7-a1063da93362
-- title:
--   Theorem 7.5.9 — the finite-state specialization recovers an ordinary finite LP
-- statement:
--   When $E$ and $A$ are both finite, the primal/dual pair of Theorem 7.5.8 collapses to an ordinary,
--   finite-dimensional linear program — genuinely the classical LP dual of $(P)$, unlike the general
--   infinite-dimensional $(D)$ (Remark 7.5.5's own caveat). In this case a stronger conclusion holds:
--   an optimal *vertex* of the dual polytope has, at every state, a unique action with positive mass,
--   and reading off that action at each state gives an optimal stationary policy directly — the
--   natural point of comparison against the platform's existing finite-dimensional LP duality
--   theorems, checked and found not directly reusable without a nontrivial reindexing bridge (see
--   `STATUS.md`).
--
--   **Moderation note.** The finite-case programs use $IM$ = all functions $E\to\mathbb R$ and $b\equiv 1$ (p. 219), the draft left both arbitrary; the model is contracting ($\beta<1$, the section's standing setting, without which the programs need not be feasible or bounded); $p$ is the initial distribution (a probability measure); b) states existence of an optimal $\mu^*$ and, for every optimal vertex, uniqueness of $a_x$ and the *optimality* of $(f^*,f^*,\dots)$, as the book states (the draft asserted that $f^*$ is a maximizer of $J_\infty$).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 219, Theorem 7.5.9

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

/-- Theorem 7.5.9 (Bäuerle–Rieder, p. 219, PDF 230). Let `E` and `A` be finite and `p(x) > 0` for
all `x \in E`. Then the following statements hold: a) `(P)` has an optimal solution `v^*` and
`v^* = J_\infty`. b) `(D)` has an optimal solution `\mu^*`. Let `\mu^*` be an optimal *vertex*
(extreme point of the feasible polytope `Z_D`, rendered via Mathlib's `Set.extremePoints`). Then
for all `x \in E`, there exists a unique `a_x \in D(x)` such that `\mu^*(x,a_x) > 0` and the
stationary policy `(f^*,f^*,\dots)` with `f^*(x) := a_x` is optimal. Extremality is stated
directly (not via Mathlib's `Set.extremePoints`, which needs a module structure `Measure` does
not have) via `ENNReal` convex weights, the natural combination structure on measures. The
finite-case programs use `IM` = all functions `E → ℝ` and the bounding function `b ≡ 1` (p. 219);
the model is contracting (`β < 1`, the standing setting of §7.5.2), `p` is the initial
distribution (a probability measure), and the conclusion for the vertex is the optimality of the
stationary policy `(f^*,f^*,…)` read off from it, as the book states. -/
theorem theorem_7_5_9 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [Fintype E]
    [Fintype A] [MeasurableSingletonClass E] [MeasurableSingletonClass A]
    (M : MarkovDecisionModel E A) (hβ : M.β < 1) (p : Measure E) [IsProbabilityMeasure p]
    (hp : ∀ x, 0 < p {x}) :
    (∃ vstar : E → ℝ, vstar ∈ ZP M Set.univ ∧
        ((∫ x, vstar x ∂p : ℝ) : EReal) = valP M Set.univ p ∧
        ∀ x, Jinf M x = (vstar x : EReal)) ∧
      (∃ μstar ∈ ZD M (fun _ => 1) Set.univ p,
        ((∫ xa, M.r xa ∂μstar : ℝ) : EReal) = valD M (fun _ => 1) Set.univ p) ∧
      (∀ μstar ∈ ZD M (fun _ => 1) Set.univ p,
        ((∫ xa, M.r xa ∂μstar : ℝ) : EReal) = valD M (fun _ => 1) Set.univ p →
        (∀ μ1 ∈ ZD M (fun _ => 1) Set.univ p, ∀ μ2 ∈ ZD M (fun _ => 1) Set.univ p,
          ∀ t : ENNReal, 0 < t → t < 1 →
          μstar = t • μ1 + (1 - t) • μ2 → μ1 = μstar ∧ μ2 = μstar) →
        (∀ x : E, ∃! a, a ∈ M.Dx x ∧ 0 < μstar {(x, a)}) ∧
          ∀ fstar : E → A, (∀ x, fstar x ∈ M.Dx x ∧ 0 < μstar {(x, fstar x)}) →
            ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.LPDuality
