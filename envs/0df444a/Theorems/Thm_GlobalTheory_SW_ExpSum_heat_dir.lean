-- Prove2me | Theorems.Thm_GlobalTheory_SW_ExpSum_heat_dir
-- name    : GlobalTheory.SW.ExpSum.heat_dir
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:39:19.960108+00:00
-- url     : https://prove2.me/theorems/b369162b-f068-4fc4-95ff-847a3e6540c8
-- title:
--   Exp Sum: heat dir
-- statement:
--   The Exp Sum construction uses the heat dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L182-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L182-L203

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
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem GlobalTheory.SW.ExpSum.heat_dir (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖)
    (Z : CF Ψ N N) (hZ : (Z : CM Ψ N N) ∈ Hn Ψ N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) :
    2 * π * I * deriv (fun s : ℂ => ∑' x, φ x * cexp (form Ψ x (Z + s • dir Ψ τ a b, z, z'))) 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' x, φ x *
        cexp (form Ψ x (Z, z + s • dir Ψ τ k a, z' + t • dir Ψ τ k b))) 0) 0 := by sorry
