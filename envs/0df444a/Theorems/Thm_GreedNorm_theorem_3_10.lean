-- Prove2me | Theorems.Thm_GreedNorm_theorem_3_10
-- name    : GreedNorm.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:08.069936+00:00
-- url     : https://prove2.me/theorems/d0c12117-7690-47e0-ab62-ee345b30bb9d
-- title:
--   Theorem 3.10 [NWF78; Căl+11] — $\alpha$-Greedy is an $\frac{\alpha}{p+\alpha}$-approximation under $p$ matroids (corrected: $h(\emptyset)\ge0$)
-- statement:
--   Let $E$ be a finite ground set, $M_1,\dots,M_p$ matroids on $E$, and $h:2^E\to\mathbb R$ monotone and submodular with $h(\emptyset)\ge0$. Let $0<\alpha\le1$. Run **$\alpha$-Greedy**: start with $A=\emptyset$ and repeatedly add an $\alpha$-augmentation of $A$ until $A$ is maximally feasible. Then for every set $O$ independent in all $M_i$,
--
--   $$
--   h(A)\ \ge\ \frac{\alpha}{p+\alpha}\,h(O).
--   $$
--
--   With $h$ the coverage of configurations, $p=2$ (Proposition 3.9) and $\alpha=1$ this yields the $\tfrac13$-approximation for ThreshBudgAlloc behind Theorem 1.3.
--
--   Differences from the source:
--   - correction: monotone submodular h → monotone submodular h with h(∅) ≥ 0; reason: counterexample: E = {a}, p = 1, M the free matroid, h(S) = |S| − 10, α = 1; the run is [a] and h({a}) = −9 < (1/2)·(−9) = h-bound for O = {a}
--   - reading: α-Greedy achieves an α/(p + α)-approximation → for every α-Greedy run with output A and every O independent in all M_i, α/(p + α)·h(O) ≤ h(A); reason: the approximation guarantee against every feasible solution, for every run (ties broken arbitrarily)
--   - encoding: α-augmentation with an approximation factor α → 0 < α ≤ 1; reason: an approximation factor of a maximization oracle lies in (0, 1]
--   - encoding: p matroid constraints → p Mathlib matroids M : Fin p → Matroid E with arbitrary ground sets; reason: a matroid whose ground set is smaller than E is the same constraint as its extension by loops; same instances
--   - encoding: F(A), the configurations whose addition keeps A feasible (including those already in A, for which A ∪ {e} = A) → Feasible M A, the elements e ∉ A with A ∪ {e} independent in every M_i; reason: an element of A has marginal 0, at most every marginal of a new element by monotonicity, so the maximum in the definition of an α-augmentation and the meaning of maximally feasible (no new element can be added) are unchanged; same runs and same guarantee
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 3.10, p.8 (PDF 10)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_GreedNorm_IsAlphaGreedyRun

namespace GreedNorm

/-- **Theorem 3.10 ([NWF78; Căl+11]): `α`-Greedy is an `α/(p+α)`-approximation for monotone
submodular maximization under `p` matroid constraints** (corrected: `h(∅) ≥ 0`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 3.10, p.8 (PDF 10): "Consider the problem of maximizing a monotone submodular
function subject to p matroid constraints. Then, the following algorithm (called α-Greedy)
achieves an α/(p + α)-approximation: start with A = ∅; then iteratively add to A an
α-augmentation of A until A is maximally feasible."

Let `E` be finite, `M_1, …, M_p` matroids on `E`, `h : 2^E → ℝ` monotone and submodular with
`h(∅) ≥ 0`, and `0 < α ≤ 1`. For every run of `α`-Greedy with output `A` and every `O`
independent in all `M_i`,
$$ h(A) \ge \frac{\alpha}{p+\alpha}\, h(O). $$

**Formalization Note** Matroids are Mathlib `Matroid E` indexed by `Fin p`; any `p ≥ 0`. The run
is `IsAlphaGreedyRun` (a list of `α`-augmentations from `∅` ending maximally feasible);
`F(A)` (`Feasible`) consists of the elements outside `A` that keep `A` independent in every
`M_i`. -/
theorem theorem_3_10 {E : Type} [Fintype E] [DecidableEq E] (p : ℕ) (M : Fin p → Matroid E)
    (h : Finset E → ℝ) (hmono : SubsamplingSM.Offline.IsMonotoneSetFn h)
    (hsub : NonmonotoneSubmod.Shared.Submodular h)
    (h0 : 0 ≤ h ∅) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (es : List E)
    (hrun : IsAlphaGreedyRun α h M es) (O : Finset E) (hO : ∀ i, (M i).Indep (↑O : Set E)) :
    α / ((p : ℝ) + α) * h O ≤ h es.toFinset := by sorry

end GreedNorm
