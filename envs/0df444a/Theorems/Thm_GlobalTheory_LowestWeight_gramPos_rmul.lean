-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_gramPos_rmul
-- name    : GlobalTheory.LowestWeight.gramPos_rmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:20:21.584212+00:00
-- url     : https://prove2.me/theorems/4a25dc45-8283-4b9d-8566-07daeb613bf7
-- title:
--   Lowest Weight: gram Pos rmul
-- statement:
--   The Lowest Weight construction uses the gram Pos rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L128-L135

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

theorem GlobalTheory.LowestWeight.gramPos_rmul {x₀ : Frame X.Ψ r}
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (y : Frame X.Ψ r) (τ : X.Ψ) :
    X.gramPos (rmul x₀ y) τ = ((mat y τ)ᵀ * diagonal (fun a : Fin r => (sgn X.p0 a : ℂ)) *
      (mat y τ).map (starRingEnd ℂ)).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le) := by sorry
