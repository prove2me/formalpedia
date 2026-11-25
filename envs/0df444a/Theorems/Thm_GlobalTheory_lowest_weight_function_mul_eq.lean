-- Prove2me | Theorems.Thm_GlobalTheory_lowest_weight_function_mul_eq
-- name    : GlobalTheory.lowest_weight_function_mul_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:56.805943+00:00
-- url     : https://prove2.me/theorems/cd3a70cd-b53b-5958-93fe-479de347e06c
-- title:
--   Global Theory: lowest weight function mul eq
-- statement:
--   The Global Theory construction uses the lowest weight function mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L315-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L315-L333

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.lowest_weight_function_mul_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hx₀' : x₀ ∈ X.dom)
    (m m' : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom) (hm' : DifferentiableOn ℂ m' X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hB' : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m' (rmul x b) = bchar la b * m' x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (hT' : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m' (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m' x) :
    ∀ x ∈ X.dom, m x * m' x₀ = m' x * m x₀ := by sorry
