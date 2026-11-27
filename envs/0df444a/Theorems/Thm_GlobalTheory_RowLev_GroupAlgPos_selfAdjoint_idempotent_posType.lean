-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_selfAdjoint_idempotent_posType
-- name    : GlobalTheory.RowLev.GroupAlgPos.selfAdjoint_idempotent_posType
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:55.29727+00:00
-- url     : https://prove2.me/theorems/d121527b-df54-4a72-aaf9-86f2c62bec7c
-- title:
--   Group Alg Pos: self Adjoint idempotent pos Type
-- statement:
--   The Group Alg Pos construction uses the self Adjoint idempotent pos Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L96-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean#L96-L110

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

theorem GlobalTheory.RowLev.GroupAlgPos.selfAdjoint_idempotent_posType : ∀ (Q : Type) [Group Q] [Finite Q],
    (∀ a : MonoidAlgebra ℂ Q, a * a = a → IsSA a →
      (∀ (m : ℕ) (x : Fin m → Q) (c : Fin m → ℂ), 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j)) ∧
        0 ≤ a.coeff 1 ∧ (a.coeff 1 = 0 → a = 0)) ∧
    (∀ z : MonoidAlgebra ℂ Q, z * z = z → (∀ a, z * a = a * z) → IsSA z) ∧
    ∀ a b : MonoidAlgebra ℂ Q, IsSA a → IsSA b → a * b = b * a → IsSA (a * b) := by sorry
