-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanSpectralCouplingNonvanishing_arrowhead_coupling_eq_zero_of_apply_eq_zero
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing.arrowhead_coupling_eq_zero_of_apply_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/4fcd9270-cb0d-4b68-975b-39cf00c88883
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing.arrowhead_coupling_eq_zero_of_apply_eq_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing.arrowhead_coupling_eq_zero_of_apply_eq_zero
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (hB : Function.Injective B)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0)
    (p : E) (hp : K p = 0) : p = 0 := by sorry
