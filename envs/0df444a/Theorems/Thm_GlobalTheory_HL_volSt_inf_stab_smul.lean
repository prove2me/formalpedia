-- Prove2me | Theorems.Thm_GlobalTheory_HL_volSt_inf_stab_smul
-- name    : GlobalTheory.HL.volSt_inf_stab_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:38:28.905141+00:00
-- url     : https://prove2.me/theorems/4253fd38-51e7-45a3-813c-6536d5023060
-- title:
--   HL: vol St inf stab smul
-- statement:
--   The HL construction uses the vol St inf stab smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommonStabilizerStabilizersCommensurableVolume.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommonStabilizerStabilizersCommensurableVolume.lean#L32-L39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PowEqZeroOfMemHermitianFrameUnipotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HaarInvVolumeConjModularCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnipotentStabilizesSomeLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolume
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
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.volSt_inf_stab_smul {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) {h : G} (hh : h ∈ H)
    (x : X) : H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by sorry
