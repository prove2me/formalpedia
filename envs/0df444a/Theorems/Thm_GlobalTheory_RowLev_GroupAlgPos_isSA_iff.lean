-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_isSA_iff
-- name    : GlobalTheory.RowLev.GroupAlgPos.isSA_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:19:41.173603+00:00
-- url     : https://prove2.me/theorems/76abe91f-c47c-400e-a2f8-b74adc826628
-- title:
--   Group Alg Pos: is SA iff
-- statement:
--   The Group Alg Pos construction uses the is SA iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L36-L44

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.GroupAlgPos
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
variable {Q : Type} [Group Q]

theorem GlobalTheory.RowLev.GroupAlgPos.isSA_iff [Finite Q] (a : MonoidAlgebra ℂ Q) : IsSA a ↔ adj a = a := by sorry
