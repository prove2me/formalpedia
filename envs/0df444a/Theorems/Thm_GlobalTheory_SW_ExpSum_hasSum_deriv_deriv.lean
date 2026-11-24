-- Prove2me | Theorems.Thm_GlobalTheory_SW_ExpSum_hasSum_deriv_deriv
-- name    : GlobalTheory.SW.ExpSum.hasSum_deriv_deriv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:46.620809+00:00
-- url     : https://prove2.me/theorems/23cdf626-332d-48e5-8fad-42c35f7b61fc
-- title:
--   Exp Sum: has Sum deriv deriv
-- statement:
--   The Exp Sum construction uses the has Sum deriv deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L68-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}

theorem GlobalTheory.SW.ExpSum.hasSum_deriv_deriv (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (v w : V)
    (hp : ∀ s : ℂ, p + s • v ∈ U) :
    HasSum (fun i => c i * L i w * L i v * cexp (L i p))
      (deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' i, c i * cexp (L i (p + s • v + t • w))) 0) 0) := by sorry
