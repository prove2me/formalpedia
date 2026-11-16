-- Prove2me | Theorems.Thm_GradSuffice_Supplement_theorem_6
-- name    : GradSuffice.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:29:59.851023+00:00
-- url     : https://prove2.me/theorems/28c0e153-c3af-42a1-897b-469151cb28b5
-- title:
--   Theorem 6, p.16 — $\lim_m\mathcal R^{(s)}_m(W)=0$ implies that $W$ is optimizable
-- statement:
--   Let $B$ be the unit ball of a real Banach space $X$ and let $W\subseteq B$ be a nonempty, symmetric ($w\in W\Rightarrow -w\in W$), closed and convex set. If
--   $$\lim_{m\to\infty}\mathcal R^{(s)}_m(W)=0,$$
--   where $\mathcal R^{(s)}_m(W)$ is the supremum of the non-dual sequential Rademacher complexity $\mathcal R^{(s)}_m(W;\bar\xi)$ over $B^\star$-valued adaptive sequences of length $m$, then $W$ is optimizable: for every $\varepsilon>0$ there is a (possibly randomized) first-order algorithm with a finite number of queries that is $\varepsilon$-accurate for every convex 1-Lipschitz objective defined on an open convex neighbourhood of $W$ and every valid oracle.
--
--   Together with Theorem 5 and Theorem 8, this shows that in the non-dual setting the vanishing of sequential Rademacher complexity, at any rate, is what governs optimizability.
--
--   **Formalization Note** Optimizability is the published `GradSuffice.Optimizable X W`.
--
--   Differences from the source:
--   - encoding: lim_{m→∞} R⁽ˢ⁾ₘ(W) = 0, R⁽ˢ⁾ₘ(W) the supremum over adaptive sequences → ∀ δ > 0, ∃ M, ∀ m ≥ M, ∀ B⋆-valued ξ of length m, seqRadW W ξ ≤ δ; reason: R⁽ˢ⁾ₘ(W) ≥ 0, and a supremum is at most δ iff every element is; same condition
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 6, p.16 (proof App. C.2, pp.43–45)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_Optimizable
import Definitions.Def_GradSuffice_Supplement_seqRadW

namespace GradSuffice.Supplement

/-- **Theorem 6 (vanishing non-dual Rademacher complexity gives optimizability).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 6, p.16:
"Let `W ⊆ B` be a nonempty, symmetric, closed, and convex set. If `lim_{m→∞} R⁽ˢ⁾ₘ(W) = 0`, then `W`
is optimizable."

**Formalization Note.** `R⁽ˢ⁾ₘ(W)` is the supremum of `R⁽ˢ⁾ₘ(W; ξ̄)` over `B⋆`-valued adaptive
sequences of length `m`; since it is nonnegative, `lim_m R⁽ˢ⁾ₘ(W) = 0` is stated as: for every
`δ > 0` there is `M` with `R⁽ˢ⁾ₘ(W; ξ̄) ≤ δ` for every `m ≥ M` and every `B⋆`-valued `ξ̄` of length
`m`. "Symmetric" is `w ∈ W → −w ∈ W`. Optimizability is the paper's (randomized) notion of p.4, the
base `GradSuffice.Optimizable X W` (objectives convex and 1-Lipschitz on an open convex
neighbourhood of `W`). -/
theorem theorem_6 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (W : Set X) (hWB : W ⊆ Metric.closedBall (0 : X) 1) (hWne : W.Nonempty)
    (hWsymm : ∀ w ∈ W, -w ∈ W) (hWclosed : IsClosed W) (hWconv : Convex ℝ W)
    (hlim : ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ → seqRadW W ξ ≤ δ) :
    Optimizable X W := by sorry

end GradSuffice.Supplement
