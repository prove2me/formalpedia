-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_Model_coeff_linForm
-- name    : GlobalTheory.ChowHt.Model.coeff_linForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:47.697386+00:00
-- url     : https://prove2.me/theorems/fb0e5b79-c4fd-423d-bb9f-357324dafb66
-- title:
--   Model: coeff lin Form
-- statement:
--   The Model construction uses the coeff lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L51-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
set_option autoImplicit false
open MvPolynomial NumberField

theorem GlobalTheory.ChowHt.Model.coeff_linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R)
    (k : Fin N) :
    (_root_.GlobalTheory.ChowHt.Model.linForm c).coeff (Finsupp.single (0, k) 1) = c k := by sorry
