-- Prove2me | Theorems.Thm_GlobalTheory_HL_FamilyVol_resQ_ne_zero
-- name    : GlobalTheory.HL.FamilyVol.resQ_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:36.186585+00:00
-- url     : https://prove2.me/theorems/8a926b98-0cef-5f12-875c-c00f543a4eb2
-- title:
--   Family Vol: res Q ne zero
-- statement:
--   The Family Vol construction uses the res Q ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFamilyTraceVolumeConst.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFamilyTraceVolumeConst.lean#L40-L45

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeTraceInitialSpanVolumeEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFamilyTraceVolumeConst
import Theorems.Thm_GlobalTheory_HL_LatDet_resQ_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FamilyVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.HL.FamilyVol.resQ_ne_zero (ϖ : 𝒪[F]) (h : Irreducible ϖ) : resQ ϖ ≠ 0 := by sorry
