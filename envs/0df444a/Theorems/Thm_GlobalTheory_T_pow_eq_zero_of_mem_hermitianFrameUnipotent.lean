-- Prove2me | Theorems.Thm_GlobalTheory_T_pow_eq_zero_of_mem_hermitianFrameUnipotent
-- name    : GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:45:34.968628+00:00
-- url     : https://prove2.me/theorems/9542a7f8-23a5-4fdc-a10f-51bc630b1b5d
-- title:
--   T: pow eq zero of mem hermitian Frame Unipotent
-- statement:
--   The T construction uses the pow eq zero of mem hermitian Frame Unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PowEqZeroOfMemHermitianFrameUnipotentStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PowEqZeroOfMemHermitianFrameUnipotentStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PowEqZeroOfMemHermitianFrameUnipotent
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PowEqZeroOfMemHermitianFrameUnipotentStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g ∈ S.N, ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by sorry
