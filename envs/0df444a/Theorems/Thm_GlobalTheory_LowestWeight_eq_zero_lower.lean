-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_eq_zero_lower
-- name    : GlobalTheory.LowestWeight.eq_zero_lower
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:18:57.208234+00:00
-- url     : https://prove2.me/theorems/92819ca5-2115-4fe3-a820-b2ade784e173
-- title:
--   Lowest Weight: eq zero lower
-- statement:
--   The Lowest Weight construction uses the eq zero lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L163-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L163-L256

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
open GlobalTheory.LowestWeight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem GlobalTheory.LowestWeight.eq_zero_lower (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (hx₀' : x₀ ∈ X.dom) (m : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (h0 : m x₀ = 0) {L : Frame X.Ψ r} (hL : ∀ τ a c, a < c → L τ a c = 0)
    (hLd : rmul x₀ L ∈ X.dom) : m (rmul x₀ L) = 0 := by sorry
