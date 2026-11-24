-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_det_mul_eq_sum_sm
-- name    : GlobalTheory.MinorFrame.det_mul_eq_sum_sm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:21.701933+00:00
-- url     : https://prove2.me/theorems/9e3b66b6-4ca8-4a69-bdf6-b2d759b5a480
-- title:
--   Minor Frame: det mul eq sum sm
-- statement:
--   The Minor Frame construction uses the det mul eq sum sm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumNormRowSubProdMinors.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumNormRowSubProdMinors.lean#L30-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial

theorem GlobalTheory.MinorFrame.det_mul_eq_sum_sm {R : Type} [CommRing R] {a d : ℕ} (A : Matrix (Fin a) (Fin d) R)
    (B : Matrix (Fin d) (Fin a) R) :
    (A * B).det = ∑ s : {s : Fin a → Fin d // StrictMono s},
      (A.submatrix id s.1).det * (B.submatrix s.1 id).det := by sorry
