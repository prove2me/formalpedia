-- Prove2me | Theorems.Thm_GlobalTheory_T_unitaryCharacterAbsScalar_basic_properties
-- name    : GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:33.187452+00:00
-- url     : https://prove2.me/theorems/4fd80529-151a-4df3-8307-9e90a7bcbbbe
-- title:
--   T: unitary Character Abs Scalar basic properties
-- statement:
--   The T construction uses the unitary Character Abs Scalar basic properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryCharacterAbsScalarBasicPropertiesStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryCharacterAbsScalarBasicPropertiesStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicPropertiesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : ResEtaPow (R := F) ⊥ χ m), sc F χ m 1 = 1 ∧ (∀ z z' : E, sc F χ m (z * z') = sc F χ m z * sc F χ m z') ∧ (∀ z : Eˣ, sc F χ m (z : E) = (χ z : ℂ) * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖sc F χ m (z : E)‖ ^ 2 = nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, sc F χ m (c (z : E))⁻¹ * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = sc F χ m (z : E)) ∧ (∀ t : Fˣ, sc F χ m (algebraMap F E t) = (sgn E t * (nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, sc F χ m ((z : E) * c (z : E)) = ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by sorry
