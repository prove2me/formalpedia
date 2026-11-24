-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unfolding_fc_col
-- name    : GlobalTheory.RootEx.Unfolding.fc_col
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:52:53.231857+00:00
-- url     : https://prove2.me/theorems/c70774c6-bc53-416b-af08-16de62e4f48f
-- title:
--   Unfolding: fc col
-- statement:
--   The Unfolding construction uses the fc col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OrbitLocallyConstant.lean#L229-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OrbitLocallyConstant.lean#L229-L265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMemSBEqOneOnCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvariaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpECutOmEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ColEInvMulAffPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RowSupportUniform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralWhittakerTwist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unfolding
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ)
  {A P P' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) {π : Representation ℂ (GL n k) P} {π' : Representation ℂ (GL n' k) P'}
  (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (φ : P') (F : A)
variable {μ σ θ b}

theorem GlobalTheory.RootEx.Unfolding.fc_col (hp : 1 ≤ p) (hc : p < c) (hμ : IsOpen (μ.ker : Set kˣ)) (hb : IsPos ψ p π σ b)
    (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ) (Φ Φχ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΦχ : ∀ l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, l Φχ =
      ∫ u : n' → k, χ u * l (omR μ (rowE (c + 1) p u, 1) Φ) ∂(Measure.pi fun _ => ν))
    (h : GL (n ⊕ Fin c) k) :
    ∫ β : n → k, fc hψ ν μ σ θ b φ F p χ hχ Φ (colE c (p + 1) β * h) ∂(Measure.pi fun _ => ν) =
      b (θ φ (opL hψ ν p (omR μ (1, h) Φχ))) (σ h F) := by sorry
