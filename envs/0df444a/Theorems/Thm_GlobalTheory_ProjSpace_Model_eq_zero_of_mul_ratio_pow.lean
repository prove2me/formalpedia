-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_Model_eq_zero_of_mul_ratio_pow
-- name    : GlobalTheory.ProjSpace.Model.eq_zero_of_mul_ratio_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:19.743805+00:00
-- url     : https://prove2.me/theorems/ebfb865e-2922-474c-99b7-d0d351fc17a3
-- title:
--   Model: eq zero of mul ratio pow
-- statement:
--   The Model construction uses the eq zero of mul ratio pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L44-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L44-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}

theorem GlobalTheory.ProjSpace.Model.eq_zero_of_mul_ratio_pow {i j : Fin (N + 1)} (hij : j ≠ i) (k : ℕ) {U : (PSpace R N).Opens}
    (hi : U ≤ chart R N i) (hj : U ≤ chart R N j) (hU : U = chart R N i ⊓ chart R N j)
    (u : Γ(PSpace R N, chart R N i)) (v : Γ(PSpace R N, chart R N j))
    (h : resG _ hi u * ratioOn U i hi j ^ (k + 1) = resG _ hj v) : u = 0 := by sorry
