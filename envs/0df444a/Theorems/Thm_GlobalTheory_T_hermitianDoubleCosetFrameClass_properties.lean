-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianDoubleCosetFrameClass_properties
-- name    : GlobalTheory.T.hermitianDoubleCosetFrameClass_properties
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:09:39.791719+00:00
-- url     : https://prove2.me/theorems/c4614a8a-3235-48d4-bb74-2722052ea3e2
-- title:
--   T: hermitian Double Coset Frame Class properties
-- statement:
--   The T construction uses the hermitian Double Coset Frame Class properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFrameClassPropertiesStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFrameClassPropertiesStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassPropertiesStatement
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

theorem GlobalTheory.T.hermitianDoubleCosetFrameClass_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by sorry
