-- Prove2me | Theorems.Thm_GlobalTheory_WeightedLS_det_eq_sum
-- name    : GlobalTheory.WeightedLS.det_eq_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:53:06.09992+00:00
-- url     : https://prove2.me/theorems/e0b595de-ff86-4f35-b075-c2f8926c4583
-- title:
--   Weighted LS: det eq sum
-- statement:
--   The Weighted LS construction uses the det eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBound.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBound.lean#L26-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}

theorem GlobalTheory.WeightedLS.det_eq_sum (L X : Matrix (Fin M) (Fin g) ℝ) (D : Fin M → ℝ) :
    (L.transpose * Matrix.diagonal D * X).det = ∑ S : {S : Finset (Fin M) // S.card = g},
      (∏ j, D (S.1.orderEmbOfFin S.2 j)) * ((L.submatrix (S.1.orderEmbOfFin S.2) id).det *
        (X.submatrix (S.1.orderEmbOfFin S.2) id).det) := by sorry
