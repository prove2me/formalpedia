-- Prove2me | Theorems.Thm_GlobalTheory_T_weil_representation_preserves_L2_space
-- name    : GlobalTheory.T.weil_representation_preserves_L2_space
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:26.415701+00:00
-- url     : https://prove2.me/theorems/abcc7d06-ed3c-476b-b984-a9fa02f31ae4
-- title:
--   T: weil representation preserves L2 space
-- statement:
--   The T construction uses the weil representation preserves L2 space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilRepresentationPreservesL2SpaceStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilRepresentationPreservesL2SpaceStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2Space
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2SpaceStatement
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

theorem GlobalTheory.T.weil_representation_preserves_L2_space : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by sorry
