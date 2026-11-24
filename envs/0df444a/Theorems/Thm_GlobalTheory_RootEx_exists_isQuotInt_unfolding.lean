-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_exists_isQuotInt_unfolding
-- name    : GlobalTheory.RootEx.exists_isQuotInt_unfolding
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:30:11.08061+00:00
-- url     : https://prove2.me/theorems/c8fae834-7283-4a05-b853-81a8e4f5a28f
-- title:
--   Root Ex: exists is Quot Int unfolding
-- statement:
--   The Root Ex construction uses the exists is Quot Int unfolding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralWhittakerTwist.lean#L27-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralWhittakerTwist.lean#L27-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralWhittakerTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.RootEx

theorem GlobalTheory.RootEx.exists_isQuotInt_unfolding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (P P' : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] (π : Representation ℂ (GL n k) P) (π' : Representation ℂ (GL n' k) P') (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (_ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ)) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : IsPos ψ p π σ b) (φ : P') (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h Ψ, Ψ.1 = opE ψ ν p (om μ 1 h Φ.1) → f h = b (θ φ Ψ) (σ h F)), ∃ z, IsQuotInt ν μX μG p f z := by sorry
