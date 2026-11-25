-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_intertwines_siegelLeviOperator
-- name    : GlobalTheory.T.fourier_intertwines_siegelLeviOperator
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:35:41.610611+00:00
-- url     : https://prove2.me/theorems/b363ba68-69df-4aaa-9cf1-c3ee24f507c9
-- title:
--   T: fourier intertwines siegel Levi Operator
-- statement:
--   The T construction uses the fourier intertwines siegel Levi Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierIntertwinesSiegelLeviOperatorStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierIntertwinesSiegelLeviOperatorStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesSiegelLeviOperator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesSiegelLeviOperatorStatement
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

theorem GlobalTheory.T.fourier_intertwines_siegelLeviOperator : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, weyl c ν * p = q * weyl c ν → ∀ φ : Matrix α ν E → ℂ, fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c q) (fou c ψ Q μ φ) := by sorry
