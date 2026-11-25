-- Prove2me | Theorems.Thm_GlobalTheory_HL_HermJacobian_coord_apply
-- name    : GlobalTheory.HL.HermJacobian.coord_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:04.114903+00:00
-- url     : https://prove2.me/theorems/4565d257-9a02-4fdb-a50c-f573f3ac6219
-- title:
--   Herm Jacobian: coord apply
-- statement:
--   The Herm Jacobian construction uses the coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMatrixCongruenceContentJacobian.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMatrixCongruenceContentJacobian.lean#L52-L55

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

theorem GlobalTheory.HL.HermJacobian.coord_apply (ω ω' e : E) (h : (ω - ω') * e = 1) (v : Fin m × Fin m → E) (i j : Fin m) :
    coord m ω ω' e h v i j =
      if i < j then v (i, j) + ω * v (j, i) else if j < i then v (j, i) + ω' * v (i, j)
      else v (i, j) := by sorry
