-- Prove2me | Theorems.Thm_MoranYanPAC_Main_small_witnesses_with_soa
-- name    : MoranYanPAC.Main.small_witnesses_with_soa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:05:33.674329+00:00
-- url     : https://prove2.me/theorems/7ab599dc-4b77-4540-b7ad-68d83ae0e0d5
-- title:
--   Lemma 6 — small witnesses with SOA equality (extends referenced witness core)
-- statement:
--   Let $H$ be nonempty with Littlestone dimension $d\ge1$. For every $h\in U$ of rank $r$, there is one finite witness $A\subseteq X$ satisfying simultaneously
--
--   $$|A|\le d-r,\quad\operatorname{LDim}(H[h,A])=r,\quad U[h,A]\cap F_r=\{h\},\quad\operatorname{SOA}_{H[h,A]}=h.$$
--
--   The dimension equality includes nonemptiness, even when $r=0$. The isolation clause excludes every other predictor of equal or higher rank agreeing on $A$. The referenced Open witness core supplies the size, dimension and isolation clauses; this full canonical extension retains them on the same witness and adds the missing SOA equality, with the source's zero tie convention. It does not assume the Open core as a new mathematical hypothesis.
--
--   Differences from the source:
--   - encoding: Littlestone dimension with empty class of dimension −1 → the published ldimBot in WithBot ℕ∞; reason: bottom represents −1 and top represents infinite dimension; finite comparisons and equalities have the same meaning
--   - encoding: finite witness set A → Finset X; reason: the same finite set is used in all four conclusions
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 6, p. 20 (PDF p. 20)

import Mathlib
import Definitions.Def_PrivLittlestone_rankOf
import Definitions.Def_MoranYanPAC_Main_SOA

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Lemma 6, p. 20. Full extension of the referenced Open witness core:
all clauses, including the SOA equality, hold for the same witness. -/
theorem small_witnesses_with_soa {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    ∀ h ∈ PrivLittlestone.localUniverse H d, ∃ A : Finset X,
      A.card ≤ d - PrivLittlestone.rankOf H d h ∧
      UnderstandingML.ldimBot (PrivLittlestone.restrictCls H h A) =
        (PrivLittlestone.rankOf H d h : WithBot ℕ∞) ∧
      {f ∈ PrivLittlestone.localUniverse H d | ∀ x ∈ A, f x = h x} ∩
        PrivLittlestone.rankLayer H d (PrivLittlestone.rankOf H d h) = {h} ∧
      SOA (PrivLittlestone.restrictCls H h A) = h := by sorry

end MoranYanPAC.Main
