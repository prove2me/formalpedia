-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_posType
-- name    : GlobalTheory.RowLev.GroupAlgPos.posType
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:24:44.273356+00:00
-- url     : https://prove2.me/theorems/8c7745da-a54e-54b7-887f-d9a22924814f
-- title:
--   Group Alg Pos: pos Type
-- statement:
--   The Group Alg Pos construction uses the pos Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L79-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L79-L94

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

theorem GlobalTheory.RowLev.GroupAlgPos.posType [Finite Q] (a : MonoidAlgebra ℂ Q) (h : a * a = a) (hs : IsSA a) (m : ℕ) (x : Fin m → Q)
    (c : Fin m → ℂ) : 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j) := by sorry
