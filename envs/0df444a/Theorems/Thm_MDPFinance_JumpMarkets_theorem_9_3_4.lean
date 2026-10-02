-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_theorem_9_3_4
-- name    : MDPFinance.JumpMarkets.theorem_9_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:20.743043+00:00
-- url     : https://prove2.me/theorems/51f6790c-b541-43dc-a951-5564be34cdc7
-- title:
--   Theorem 9.3.4 — the terminal wealth problem in a pure jump market (six parts)
-- statement:
--   **Theorem 9.3.4** (pp. 287-288). The main result for the terminal wealth problem.
--
--   a) The value function $V(t,x)$ of the terminal wealth problem satisfies $V = J_\infty = J \in IM_{cv}$
--      where $J := \lim_{n\to\infty}\mathcal{T}^n U$.
--   b) $V(t,x)$ is the unique fixed point of $\mathcal{T}$ in $IM_{cv}$.
--   c) It holds for $g \in IM_{cv}$ that
--      $\|V - \mathcal{T}^n g\|_b \le \frac{\alpha_b^n}{1-\alpha_b}\|\mathcal{T}g - g\|_b$.
--   d) There exists an optimal Markov portfolio strategy $\pi^* = (\pi^*_t)$ such that
--      $\pi^*_t = f^*(T_n, Z_n)(t - T_n)$, $t \in (T_n, T_{n+1}]$, for a decision rule
--      $f^* : E \to A$.
--   e) The policy iteration holds.
--   f) Howard's policy improvement algorithm holds.
--
--   **The theorem has six parts, not three.** Parts d), e) and f) are on PDF p. 298, across the page
--   break from a)-c); both the extracted statement file and this chunk's planning brief stop after c).
--   Part d) is cited by name later in the section ("The stationary policy $(f^*,f^*,\dots)$ defines an
--   optimal portfolio strategy (see Theorem 9.3.4 d))", p. 289), which is what exposed the truncation.
--   A formalization of a)-c) alone would omit the entire *control* half: those three parts say only
--   what the value function is and how fast value iteration converges to it, and never produce a
--   portfolio strategy.
--
--   The shape is Chapter 7's Structure Theorem delivered for a concrete market: existence, uniqueness,
--   and an explicit geometric rate.
--
--   Three points of care. $\mathcal{T}$ is a supremum over $A$ and is carried as a relation defined by
--   `IsLUB`, never `sSup`, which for an unbounded set is $0$ — a live risk since the reward is
--   unbounded. c) is stated in its $\le$-form against the bounding function rather than by forming
--   $\|\cdot\|_b$, itself a supremum. And d)'s optimality is **attainment** — the stationary policy's
--   value *equals* $V$ — not an inequality, which every policy satisfies by definition.
--
--   e)'s $\mathrm{Ls}$ is taken in the Young topology on $A$, the one Remark 8.2.3 uses and in which
--   the relaxed controls are compact; it is carried as an instance argument rather than constructed.
--   $\mathrm{Ls}\,D_n$ is the book's own definition (p. 201) — an accumulation point of *some*
--   sequence $(a_n)$ with $a_n \in D_n$ — a statement about points, not a `Filter.limsup` of sets.
--
--   **Moderation note.** The draft's a) omitted `V = J_∞` (it had no `J_∞`), its `V` was a real supremum over Markov strategies only, d)'s `f^*` was not required measurable, e) was quantified over an arbitrary topology on `A` (refutable, see the model item) and f) assumed `J_f = 𝒯_f J_f` as a hypothesis and stated an improvement inequality unlike Theorem 7.5.1. Now: a) `V = J_∞ = J ∈ IM_cv` with `J = lim 𝒯^n U`; b) uniqueness in `IM_cv`; c) the rate; d) a measurable maximizer `f^*` whose stationary policy attains `V`; e) `∅ ≠ Ls A^*_{J_n}(t,x) ⊂ A^*_V(t,x)` over the relaxed controls with the Young topology; f) Theorem 7.5.1 a) and c): an improvement on a measurable `E_0` is strict there, and a decision rule with no improvement is optimal.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, pp. 287-288 (PDF 297-298), Theorem 9.3.4

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- **Theorem 9.3.4** (pp. 287-288), under a bounding function `b = b_γ` with `α_b < 1` (the
standing assumption "γ large enough"). a) `V = J_∞ = J ∈ IM_cv`, `J := lim_n 𝒯^n U`.
b) `V` is the unique fixed point of `𝒯` in `IM_cv`. c) For `g ∈ IM_cv`: `‖V - 𝒯^n g‖_b ≤
(α_b^n/(1-α_b)) ‖𝒯g - g‖_b` (in `≤`-form against `b`). d) There is an optimal Markov portfolio
strategy `π^*_t = f^*(T_n,Z_n)(t - T_n)` for a decision rule `f^* : E → A` (measurable,
a maximizer of `V`, whose stationary policy attains `V`). e) Policy iteration (Theorem 7.3.6 c),
in the Young topology on the relaxed controls `R`): `∅ ≠ Ls A^*_{J_n}(t,x) ⊂ A^*_V(t,x)`.
f) Howard's policy improvement (Theorem 7.5.1 a), c)): an improvement `h` of `f` on a
measurable `E_0` has `J_h ≥ J_f` with strict inequality on `E_0`, and if no improvement of `f`
exists then `J_f = J_∞`. -/
theorem theorem_9_3_4 {d : ℕ} (M : JumpMarket d) (gamma alpha : ℝ)
    (hb : M.IsBoundingFunction (M.bfun gamma) alpha) (halpha0 : 0 ≤ alpha) (halpha : alpha < 1)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    ∃ v : ℝ × ℝ → ℝ, M.IMcv (M.bfun gamma) v ∧
      (∀ p ∈ M.E, M.V Pr p = ENNReal.ofReal (v p)) ∧
      (∀ p ∈ M.E, M.Jinf Pr p = ENNReal.ofReal (v p)) ∧
      (∀ h : ℕ → ℝ × ℝ → ℝ, M.IsTChain (fun p => M.U p.2) h →
        ∀ p ∈ M.E, Tendsto (fun n => h n p) atTop (𝓝 (v p))) ∧
      (M.IsTOf v v ∧
        ∀ w : ℝ × ℝ → ℝ, M.IMcv (M.bfun gamma) w → M.IsTOf w w → ∀ p ∈ M.E, w p = v p) ∧
      (∀ (g : ℝ × ℝ → ℝ) (h : ℕ → ℝ × ℝ → ℝ) (C : ℝ),
        M.IMcv (M.bfun gamma) g → M.IsTChain g h →
        (∀ p ∈ M.E, |h 1 p - g p| ≤ C * M.bfun gamma p) →
        ∀ (n : ℕ), ∀ p ∈ M.E,
          |v p - h n p| ≤ (alpha ^ n / (1 - alpha)) * C * M.bfun gamma p) ∧
      (∃ fstar : ℝ × ℝ → Control d, Measurable fstar ∧
        (∀ p ∈ M.E, fstar p ∈ M.Astar (fun q => ENNReal.ofReal (v q)) p) ∧
        ∀ p ∈ M.E, M.Jstat Pr fstar p = M.V Pr p) ∧
      (∀ h : ℕ → ℝ × ℝ → ℝ, M.IsTChain (fun p => M.U p.2) h →
        ∀ p ∈ M.E,
          (LsSeq (fun n => M.AstarRel (fun q => ENNReal.ofReal (h n q)) p)).Nonempty ∧
          LsSeq (fun n => M.AstarRel (fun q => ENNReal.ofReal (h n q)) p) ⊆
            M.AstarRel (fun q => ENNReal.ofReal (v q)) p) ∧
      (∀ f h : ℝ × ℝ → Control d, Measurable f → Measurable h →
        ∀ E0 : Set (ℝ × ℝ), MeasurableSet E0 →
          (∀ p ∈ M.E, p ∈ E0 → M.Jstat Pr f p < M.L (M.Jstat Pr f) (h p) p) →
          (∀ p ∈ M.E, p ∉ E0 → h p = f p) →
          (∀ p ∈ M.E, M.Jstat Pr f p ≤ M.Jstat Pr h p) ∧
            ∀ p ∈ M.E, p ∈ E0 → M.Jstat Pr f p < M.Jstat Pr h p) ∧
      (∀ f : ℝ × ℝ → Control d, Measurable f →
        (∀ p ∈ M.E, ∀ a : Control d, M.L (M.Jstat Pr f) a p ≤ M.Jstat Pr f p) →
        ∀ p ∈ M.E, M.Jstat Pr f p = M.Jinf Pr p) := by sorry

end MDPFinance.JumpMarkets
