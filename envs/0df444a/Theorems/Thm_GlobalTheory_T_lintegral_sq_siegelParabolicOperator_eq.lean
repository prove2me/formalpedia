-- Prove2me | Theorems.Thm_GlobalTheory_T_lintegral_sq_siegelParabolicOperator_eq
-- name    : GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:03.4048+00:00
-- url     : https://prove2.me/theorems/1b28cb51-3dd9-455e-8579-9562c113d561
-- title:
--   T: lintegral sq siegel Parabolic Operator eq
-- statement:
--   The T construction uses the lintegral sq siegel Parabolic Operator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralSqSiegelParabolicOperatorEqStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralSqSiegelParabolicOperatorEqStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralSqSiegelParabolicOperatorEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralSqSiegelParabolicOperatorEqStatement
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

theorem GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by sorry
