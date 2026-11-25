-- Prove2me | Theorems.Thm_GlobalTheory_HL_span_pointwise_le_of_int
-- name    : GlobalTheory.HL.span_pointwise_le_of_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:13.350603+00:00
-- url     : https://prove2.me/theorems/f64a485c-eefa-5c29-8f9d-fa8c7232a595
-- title:
--   HL: span pointwise le of int
-- statement:
--   The HL construction uses the span pointwise le of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemStabilizerSpanIffUnitriangularIntegral.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemStabilizerSpanIffUnitriangularIntegral.lean#L11-L23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemStabilizerSpanIffUnitriangularIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.span_pointwise_le_of_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E)
    (h : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E) (hM : IsIntM L M)
    (hv : ∀ b, h (v b) = ∑ a, M a b • v a) :
    h • Submodule.span L.O (Set.range v) ≤ Submodule.span L.O (Set.range v) := by sorry
