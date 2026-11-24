-- Prove2me | Theorems.Thm_GlobalTheory_KSp_sc_basic
-- name    : GlobalTheory.KSp.sc_basic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:38.374799+00:00
-- url     : https://prove2.me/theorems/bd1a6c71-4ffe-4eaf-a5f3-7476126a61fb
-- title:
--   KSp: sc basic
-- statement:
--   The KSp construction uses the sc basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryCharacterAbsScalarBasicProperties.lean#L43-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryCharacterAbsScalarBasicProperties.lean#L43-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicProperties
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
open GlobalTheory GlobalTheory.KSp
open MeasureTheory Matrix

theorem GlobalTheory.KSp.sc_basic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : _root_.GlobalTheory.WeilM.ResEtaPow (R := F) ⊥ χ m), _root_.GlobalTheory.KSp.sc F χ m 1 = 1 ∧ (∀ z z' : E, _root_.GlobalTheory.KSp.sc F χ m (z * z') = _root_.GlobalTheory.KSp.sc F χ m z * _root_.GlobalTheory.KSp.sc F χ m z') ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖_root_.GlobalTheory.KSp.sc F χ m (z : E)‖ ^ 2 = _root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (c (z : E))⁻¹ * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = _root_.GlobalTheory.KSp.sc F χ m (z : E)) ∧ (∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) = (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m ((z : E) * c (z : E)) = ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by sorry
