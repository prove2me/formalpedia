-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_posDef_contract
-- name    : GlobalTheory.LowestWeight.posDef_contract
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:19:53.160355+00:00
-- url     : https://prove2.me/theorems/847d315c-b01b-4c92-a292-236a621eb2ec
-- title:
--   Lowest Weight: pos Def contract
-- statement:
--   The Lowest Weight construction uses the pos Def contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L46-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L46-L70

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
variable {r : ℕ}

theorem GlobalTheory.LowestWeight.posDef_contract {p : ℕ} (e : Fin p → Fin r) (p0 : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (t : Fin r → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (h1 : ∀ a : Fin r, (a : ℕ) < p0 → ρ ≤ ‖t a‖)
    (h2 : ∀ a : Fin r, p0 ≤ (a : ℕ) → ‖t a‖ ≤ ρ)
    (hY : ((Yᵀ * diagonal (fun a : Fin r => (sgn p0 a : ℂ)) *
      Y.map (starRingEnd ℂ)).submatrix e e).PosDef) :
    (((diagonal t * Y)ᵀ * diagonal (fun a : Fin r => (sgn p0 a : ℂ)) *
      (diagonal t * Y).map (starRingEnd ℂ)).submatrix e e).PosDef := by sorry
