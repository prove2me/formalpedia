-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_corollary_11_moreover
-- name    : MultiAllocToAlloc.Subadditive.corollary_11_moreover
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:10:36.845805+00:00
-- url     : https://prove2.me/theorems/4fd32e6e-f3cf-45dc-9bf3-318e16d09249
-- title:
--   Corollary 11 (Moreover and parenthetical, as printed) — ω(S_q, M, v) ≥ MMS(M, v, 2) and ω(S_p, M, v) ≥ MMS(M, v, 2)
-- statement:
--   Let $M$ be a finite set of items and $v$ a valuation. A valuation v assigns a real number to every set of items and is normalized (v(∅) = 0) and monotone (v(S) ≤ v(T) for S ⊆ T), the paper's standing assumptions (p. 1, and §2.1, p. 6); it is subadditive when v(S ∪ T) ≤ v(S) + v(T) for all S, T. Here ω(S_p, M, v) and ω(S_q, M, v) (Definition 7, p. 6) are the maximin values that a player p with valuation v (her payoff is v(T) for the set T of items she picks; the opponent q's payoff is −v(T)) can guarantee in the picking game on the finite item set M with the alternating picking sequence of length |M| that starts with p (S_p) or with q (S_q); every item of M is picked. $\mathrm{MMS}(M,v,2)$ is the maximin share of $M$ for two bundles: the maximum, over all ways of splitting $M$ into two labelled, possibly empty bundles $P_1,P_2$, of $\min(v(P_1),v(P_2))$ (`LittleCharity.MMS.mms v 2 M`). As printed: if $v$ is subadditive and no single item of $M$ has value larger than $\delta$ ($v(\{e\})\le\delta$ for every $e\in M$), then
--   $$\omega(S_q,M,v)\ \ge\ \mathrm{MMS}(M,v,2)\qquad\text{and}\qquad \omega(S_p,M,v)\ \ge\ \mathrm{MMS}(M,v,2).$$
--   This is the second sentence of Corollary 11 together with its parenthetical, stated exactly as printed. The q-first inequality is false even for additive valuations; the p-first inequality is false for subadditive valuations, although it holds for additive valuations; the counterexamples, and the corrected forms with a factor $\tfrac12$, are recorded as findings, not in this statement.
--
--   Differences from the source:
--   - encoding: a valuation v defined on the subsets of the game's item set M → v : Finset (Fin m) → ℝ defined on all subsets of the ambient items Fin m, with M : Finset (Fin m) and the normalization, monotonicity (and subadditivity) hypotheses stated for all subsets; reason: ω(S, M, v) depends only on the values of v on subsets of M, and every normalized monotone (subadditive) valuation on the subsets of M extends to Fin m with the same properties via T ↦ v(T ∩ M); same instances
--   - reading: MMS(M, v_i, 2) → LittleCharity.MMS.mms v 2 M, i.e. MMS(M, v, 2) for the corollary's own valuation v; reason: the corollary has a single valuation v and no agent i; the subscript i is a notation slip (INSIGHTS I4)
-- source:
--   Feige, arXiv:2506.21493v1, Corollary 11, p. 8

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame

namespace MultiAllocToAlloc.Subadditive

/-- Feige, arXiv:2506.21493v1, Corollary 11 (second sentence and parenthetical), p. 8, as
printed: under the hypotheses of Corollary 11, `ω(S_q, M, v) ≥ MMS(M, v, 2)` and
`ω(S_p, M, v) ≥ MMS(M, v, 2)`. (False as printed; see the chunk's INSIGHTS I1, I2.) -/
theorem corollary_11_moreover {m : ℕ} (M : Finset (Fin m)) (v : Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotone v) (hsub : SubmodOrder.Subadditive v)
    (δ : ℝ) (hδ : ∀ e ∈ M, v {e} ≤ δ) :
    LittleCharity.MMS.mms v 2 M ≤ omegaQ v M ∧ LittleCharity.MMS.mms v 2 M ≤ omegaP v M := by sorry

end MultiAllocToAlloc.Subadditive
