-- Prove2me | Theorems.Thm_GlobalTheory_HL_HermJacobian_det_of_comm
-- name    : GlobalTheory.HL.HermJacobian.det_of_comm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:34:06.739816+00:00
-- url     : https://prove2.me/theorems/fcedbcbf-64ef-5e1e-8083-72415d83ba0b
-- title:
--   Herm Jacobian: det of comm
-- statement:
--   The Herm Jacobian construction uses the det of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMatrixCongruenceContentJacobian.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMatrixCongruenceContentJacobian.lean#L88-L103

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical Kronecker
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.HermJacobian
variable {E : Type} [CommRing E] {m : ℕ}

theorem GlobalTheory.HL.HermJacobian.det_of_comm {F : Type} [Field F] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → F) →ₗ[F] (ι → F)) (g : (ι → E) →ₗ[E] (ι → E))
    (h : ∀ v, g (fun k => algebraMap F E (v k)) = fun k => algebraMap F E (f v k)) :
    algebraMap F E (LinearMap.det f) = LinearMap.det g := by sorry
