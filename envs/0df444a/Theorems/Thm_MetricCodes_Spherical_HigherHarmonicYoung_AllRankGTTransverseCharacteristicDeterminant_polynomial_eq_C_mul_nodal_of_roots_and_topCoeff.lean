-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseCharacteristicDeterminant_polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant.polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:10.573365+00:00
-- url     : https://prove2.me/theorems/92a054ad-822b-4c04-b799-dbdaef1a0dfc
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant.polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant.polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (hinj : Function.Injective nodes)
    (P : Polynomial ℝ) (c : ℝ)
    (hdeg : P.degree < Fintype.card ι + 1)
    (hcoeff : P.coeff (Fintype.card ι) = c)
    (hroot : ∀ i : ι, P.eval (nodes i) = 0) :
    P = Polynomial.C c * Lagrange.nodal Finset.univ nodes := by sorry
