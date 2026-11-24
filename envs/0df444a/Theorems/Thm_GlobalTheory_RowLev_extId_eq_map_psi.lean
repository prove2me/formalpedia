-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_extId_eq_map_psi
-- name    : GlobalTheory.RowLev.extId_eq_map_psi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:32:54.973503+00:00
-- url     : https://prove2.me/theorems/cec3f1d9-97bb-43f0-be74-c014b0f5fe97
-- title:
--   Row Lev: ext Id eq map psi
-- statement:
--   The Row Lev construction uses the ext Id eq map psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtIdMulSupNatCastConj.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtIdMulSupNatCastConj.lean#L11-L19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntAfApproxInterUnitConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtIdMulSupNatCastConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev

theorem GlobalTheory.RowLev.extId_eq_map_psi (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by sorry
