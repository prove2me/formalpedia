-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_SqfCrt_extId_eq_image
-- name    : GlobalTheory.RowLev.SqfCrt.extId_eq_image
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:32:59.056676+00:00
-- url     : https://prove2.me/theorems/02fe0742-aa52-4071-b8b9-c08f54464317
-- title:
--   Sqf Crt: ext Id eq image
-- statement:
--   The Sqf Crt construction uses the ext Id eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsProdLeOfIsRadical.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsProdLeOfIsRadical.lean#L46-L55

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsProdLeOfIsRadical
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
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.SqfCrt

theorem GlobalTheory.RowLev.SqfCrt.extId_eq_image (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by sorry
