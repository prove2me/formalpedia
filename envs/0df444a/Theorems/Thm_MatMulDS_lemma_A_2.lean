-- Prove2me | Theorems.Thm_MatMulDS_lemma_A_2
-- name    : MatMulDS.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:15.227415+00:00
-- url     : https://prove2.me/theorems/d71f4303-acd2-4da2-b4b7-e017293ea76f
-- title:
--   Lemma A.2 — sizes of an identity; a private map exists
-- statement:
--   Let an approximate bilinear identity compute a block tensor, with left variables $X$, right variables $Y$, outputs $O$ and $P_{\mathrm{base}}$ products. Then
--   $$|X|,|Y|,|O|\le P_{\mathrm{base}},$$
--   every output $o$ has at least $\mathrm{len}(o)$ relevant products, and the identity has a private map.
--
--   So an identity cannot be smaller than its tensor in any direction, and the private map used in the construction always exists.
--
--   Differences from the source: none.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma A.2, p.67 (PDF p.69)

import Mathlib
import Definitions.Def_MatMulDS_IdentityData

set_option autoImplicit false

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Lemma A.2 (Sizes of the Identity), p.67** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file
sha256 6c5a1c16…). `|X|, |Y|, |O| ≤ P_base`, every output `o` has at least `len(o)` relevant products, and the identity
has a private map. -/
theorem lemma_A_2 (T : BlockTensor I K J B) (D : IdentityData I K J P) (hD : D.Computes T) :
    T.leftVars.card ≤ Fintype.card P ∧ T.rightVars.card ≤ Fintype.card P ∧
    T.outputs.card ≤ Fintype.card P ∧
    (∀ o ∈ T.outputs, T.len o ≤ (D.Prel o).card) ∧
    ∃ ρ : T.Out → P, D.IsPrivateMap T ρ := by sorry

end MatMulDS
