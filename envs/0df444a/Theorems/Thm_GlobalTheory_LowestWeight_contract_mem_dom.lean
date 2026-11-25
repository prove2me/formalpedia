-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_contract_mem_dom
-- name    : GlobalTheory.LowestWeight.contract_mem_dom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:15:20.612571+00:00
-- url     : https://prove2.me/theorems/cdf4fd16-a372-4cbc-b75f-eeb36917ddae
-- title:
--   Lowest Weight: contract mem dom
-- statement:
--   The Lowest Weight construction uses the contract mem dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L137-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L137-L153

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

theorem GlobalTheory.LowestWeight.contract_mem_dom {x₀ : Frame X.Ψ r}
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    {y : Frame X.Ψ r} (hy : rmul x₀ y ∈ X.dom) (t : Fin r → ℂ) (ht : ∀ a, t a ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) (h1 : ∀ a : Fin r, (a : ℕ) < X.p0 → ρ ≤ ‖t a‖)
    (h2 : ∀ a : Fin r, X.p0 ≤ (a : ℕ) → ‖t a‖ ≤ ρ) :
    rmul x₀ (fun τ => (diagonal t * mat y τ : Matrix (Fin r) (Fin r) ℂ)) ∈ X.dom := by sorry
