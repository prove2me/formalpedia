-- Prove2me | Theorems.Thm_MoranYanPAC_Main_dimension_decreases_with_rank
-- name    : MoranYanPAC.Main.dimension_decreases_with_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:05:16.687717+00:00
-- url     : https://prove2.me/theorems/a42007c8-f8e6-4066-a6cf-451412d408f9
-- title:
--   Lemma 4 — dimension decreases with rank
-- statement:
--   Fix a nonempty binary class $H$ of Littlestone dimension $d\ge1$, with local universe $U$ and recursively defined rank layers $F_s$. For every integer $0\le s\le d$,
--
--   $$\operatorname{LDim}(F_s)\le d-s,\qquad\operatorname{LDim}(U)=d.$$
--
--   The equality is included as well as every layer bound. These dimensions describe the source's constructed classes rather than arbitrary classes supplied with a dimension certificate.
--
--   Differences from the source:
--   - encoding: Littlestone dimension with empty class of dimension −1 → the published ldimBot in WithBot ℕ∞; reason: bottom represents −1 and top represents infinite dimension; finite comparisons and equalities have the same meaning
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 4, p. 20 (PDF p. 20)

import Mathlib
import Definitions.Def_PrivLittlestone_rankLayer

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Lemma 4, p. 20, including the equality for the local universe. -/
theorem dimension_decreases_with_rank {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    (∀ s : ℕ, s ≤ d →
      UnderstandingML.ldimBot (PrivLittlestone.rankLayer H d s) ≤
        ((d - s : ℕ) : WithBot ℕ∞)) ∧
    UnderstandingML.ldimBot (PrivLittlestone.localUniverse H d) = (d : WithBot ℕ∞) := by sorry

end MoranYanPAC.Main
