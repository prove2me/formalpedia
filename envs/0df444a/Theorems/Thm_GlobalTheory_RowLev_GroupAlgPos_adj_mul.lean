-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_adj_mul
-- name    : GlobalTheory.RowLev.GroupAlgPos.adj_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:46.546356+00:00
-- url     : https://prove2.me/theorems/9c3c2e72-c8d8-4794-b122-5705039d0d2f
-- title:
--   Group Alg Pos: adj mul
-- statement:
--   The Group Alg Pos construction uses the adj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L23-L28

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

theorem GlobalTheory.RowLev.GroupAlgPos.adj_mul [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a * b) = adj b * adj a := by sorry
