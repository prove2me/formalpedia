-- Prove2me | Theorems.Thm_MoranYanPAC_Main_dimension_inside_witness
-- name    : MoranYanPAC.Main.dimension_inside_witness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:09.201576+00:00
-- url     : https://prove2.me/theorems/275485ac-273f-4652-a62e-2ccd34e34b04
-- title:
--   Lemma 7 — dimension inside a witness version space
-- statement:
--   Fix a nonempty $H$ with Littlestone dimension $d\ge1$ and the sample-independent witnesses furnished by Lemma 6. For $h\in U$ write $r=\rho(h)$ and $Q_h=U[h,A_h]$. For every $0\le s\le r$,
--
--   $$\operatorname{LDim}(Q_h\cap F_s)\le r-s,\qquad Q_h\cap F_r=\{h\}.$$
--
--   The singleton conclusion is retained explicitly. The witnesses are fixed data from the source preamble, including the SOA clause, and cannot change between samples.
--
--   Differences from the source:
--   - encoding: Littlestone dimension with empty class of dimension −1 → the published ldimBot in WithBot ℕ∞; reason: bottom represents −1 and top represents infinite dimension; finite comparisons and equalities have the same meaning
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 7, p. 22 (PDF p. 22)

import Mathlib
import Definitions.Def_MoranYanPAC_Main_Candidates

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Lemma 7, p. 22: local dimension and the singleton clause. -/
theorem dimension_inside_witness {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (h : X → Bool) (hh : h ∈ PrivLittlestone.localUniverse H d) :
    (∀ s : ℕ, s ≤ PrivLittlestone.rankOf H d h →
      UnderstandingML.ldimBot (PrivLittlestone.witnessSpace H d Aw h ∩
        PrivLittlestone.rankLayer H d s) ≤
          ((PrivLittlestone.rankOf H d h - s : ℕ) : WithBot ℕ∞)) ∧
    PrivLittlestone.witnessSpace H d Aw h ∩
      PrivLittlestone.rankLayer H d (PrivLittlestone.rankOf H d h) = {h} := by sorry

end MoranYanPAC.Main
