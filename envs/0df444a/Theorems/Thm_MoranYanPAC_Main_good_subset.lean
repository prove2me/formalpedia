-- Prove2me | Theorems.Thm_MoranYanPAC_Main_good_subset
-- name    : MoranYanPAC.Main.good_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:05:35.651394+00:00
-- url     : https://prove2.me/theorems/b1f60dfb-39d3-4187-98d4-7eb09e00fbfd
-- title:
--   Lemma 8 — a large good subset
-- statement:
--   Let $d\ge1$ be the ambient parameter defining goodness. Every finite nonempty family $G$ of binary predictors with $\operatorname{LDim}(G)\le t$, for any integer $t\ge0$, contains a nonempty good subset $G'\subseteq G$ such that
--
--   $$|G'|\ge\frac{|G|}{[2(d+1)]^t}.$$
--
--   The family need not lie in the local universe $U$, and $t$ need not be at most $d$. Goodness is the strict pointwise threshold fixed in Section 7.2. The case $t=0$ is part of the statement.
--
--   Differences from the source:
--   - encoding: finite families of distinct predictors → Finset of functions with extensional equality; reason: this represents exactly the source finite sets, independently of repeated observations
--   - encoding: Littlestone dimension with empty class of dimension −1 → the published ldimBot in WithBot ℕ∞; reason: bottom represents −1 and top represents infinite dimension; finite comparisons and equalities have the same meaning
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 8, p. 23 (PDF p. 23)

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_MoranYanPAC_Main_GoodFamily

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Lemma 8, p. 23. G need not be contained in U; t has no upper bound. -/
theorem good_subset {X : Type*} (d : ℕ) (hd1 : 1 ≤ d)
    (G : Finset (X → Bool)) (hG : G.Nonempty) (t : ℕ)
    (ht : UnderstandingML.ldimBot (G : Set (X → Bool)) ≤ (t : WithBot ℕ∞)) :
    ∃ G' : Finset (X → Bool), G' ⊆ G ∧ Good d G' ∧
      (G.card : ℝ) / (2 * ((d : ℝ) + 1)) ^ t ≤ G'.card := by sorry

end MoranYanPAC.Main
