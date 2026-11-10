-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_corollary_11
-- name    : MultiAllocToAlloc.Subadditive.corollary_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:10:28.351105+00:00
-- url     : https://prove2.me/theorems/82d6dcf7-2117-4c8b-9477-97e5bb3613e3
-- title:
--   Corollary 11 (first sentence) — ω(S_p, M, v) ≥ v(M)/2 and ω(S_q, M, v) ≥ (v(M) − δ)/2
-- statement:
--   Let $M$ be a finite set of items and $v$ a valuation. A valuation v assigns a real number to every set of items and is normalized (v(∅) = 0) and monotone (v(S) ≤ v(T) for S ⊆ T), the paper's standing assumptions (p. 1, and §2.1, p. 6); it is subadditive when v(S ∪ T) ≤ v(S) + v(T) for all S, T. Here ω(S_p, M, v) and ω(S_q, M, v) (Definition 7, p. 6) are the maximin values that a player p with valuation v (her payoff is v(T) for the set T of items she picks; the opponent q's payoff is −v(T)) can guarantee in the picking game on the finite item set M with the alternating picking sequence of length |M| that starts with p (S_p) or with q (S_q); every item of M is picked. If $v$ is subadditive and no single item of $M$ has value larger than $\delta$ (that is, $v(\{e\})\le\delta$ for every $e\in M$), then
--   $$\omega(S_p,M,v)\ \ge\ \tfrac12\,v(M)\qquad\text{and}\qquad \omega(S_q,M,v)\ \ge\ \frac{v(M)-\delta}{2}.$$
--   This first sentence is stated as printed, including the empty-set corner: when $M=\emptyset$, $v=0$ and $\delta=-1$, its second bound is false (INSIGHTS I5). The second and third sentences of Corollary 11 are the separate item `corollary_11_moreover`.
--
--   Differences from the source:
--   - encoding: a valuation v defined on the subsets of the game's item set M → v : Finset (Fin m) → ℝ defined on all subsets of the ambient items Fin m, with M : Finset (Fin m) and the normalization, monotonicity (and subadditivity) hypotheses stated for all subsets; reason: ω(S, M, v) depends only on the values of v on subsets of M, and every normalized monotone (subadditive) valuation on the subsets of M extends to Fin m with the same properties via T ↦ v(T ∩ M); same instances
-- source:
--   Feige, arXiv:2506.21493v1, Corollary 11, p. 8

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame

namespace MultiAllocToAlloc.Subadditive

/-- Feige, arXiv:2506.21493v1, Corollary 11 (first sentence), p. 8: if `v` is (normalized,
monotone and) subadditive and no single item of `M` has value larger than `δ`, then
`ω(S_p, M, v) ≥ v(M)/2` and `ω(S_q, M, v) ≥ (v(M) − δ)/2`. -/
theorem corollary_11 {m : ℕ} (M : Finset (Fin m)) (v : Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotone v) (hsub : SubmodOrder.Subadditive v)
    (δ : ℝ) (hδ : ∀ e ∈ M, v {e} ≤ δ) :
    v M / 2 ≤ omegaP v M ∧ (v M - δ) / 2 ≤ omegaQ v M := by sorry

end MultiAllocToAlloc.Subadditive
