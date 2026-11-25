-- Prove2me | Theorems.Thm_GlobalTheory_mem_nonzeroLocus_iff_mem_basicOpen_chart
-- name    : GlobalTheory.mem_nonzeroLocus_iff_mem_basicOpen_chart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:09.694649+00:00
-- url     : https://prove2.me/theorems/92b8115b-bcfc-4c7f-9850-49dae4767876
-- title:
--   Global Theory: mem nonzero Locus iff mem basic Open chart
-- statement:
--   The Global Theory construction uses the mem nonzero Locus iff mem basic Open chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemNonzeroLocusIffMemBasicOpenChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory

theorem GlobalTheory.mem_nonzeroLocus_iff_mem_basicOpen_chart {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι)
    {x : Y} (hk : x ∈ H.U k) : x ∈ nonzeroLocus s ↔ x ∈ Y.basicOpen (s.f k) := by sorry
