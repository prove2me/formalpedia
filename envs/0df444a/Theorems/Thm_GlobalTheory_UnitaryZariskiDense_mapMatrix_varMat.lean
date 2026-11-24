-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_mapMatrix_varMat
-- name    : GlobalTheory.UnitaryZariskiDense.mapMatrix_varMat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:51.181151+00:00
-- url     : https://prove2.me/theorems/2a91161b-caa1-40f5-aaac-5419fdb7821c
-- title:
--   Unitary Zariski Dense: map Matrix var Mat
-- statement:
--   The Unitary Zariski Dense construction uses the map Matrix var Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L137-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}

theorem GlobalTheory.UnitaryZariskiDense.mapMatrix_varMat (x : ι × Fin a × Fin a → ℂ) (τ : ι) :
    (eval x).mapMatrix (varMat (a := a) τ) = famOf x τ := by sorry
