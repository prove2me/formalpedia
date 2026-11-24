-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_Model_resG_overlap_injective
-- name    : GlobalTheory.ProjSpace.Model.resG_overlap_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:16.491801+00:00
-- url     : https://prove2.me/theorems/60e93069-c387-4a8e-a371-84b7df730b69
-- title:
--   Model: res G overlap injective
-- statement:
--   The Model construction uses the res G overlap injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L27-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L27-L42

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

theorem GlobalTheory.ProjSpace.Model.resG_overlap_injective (i j : Fin (N + 1)) {U : (PSpace R N).Opens} (hi : U ≤ chart R N i)
    (hU : U = chart R N i ⊓ chart R N j) : Function.Injective (resG (PSpace R N) hi) := by sorry
