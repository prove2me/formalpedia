-- Prove2me | Theorems.Thm_GlobalTheory_mem_basicOpen_finset_prod_iff
-- name    : GlobalTheory.mem_basicOpen_finset_prod_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:51:27.740805+00:00
-- url     : https://prove2.me/theorems/4ab4ad71-4ad5-4083-b78f-e359b348da31
-- title:
--   Global Theory: mem basic Open finset prod iff
-- statement:
--   The Global Theory construction uses the mem basic Open finset prod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L22-L30

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

theorem GlobalTheory.mem_basicOpen_finset_prod_iff {Y : Scheme.{0}} {U : Y.Opens} {ι : Type} (f : ι → Γ(Y, U))
    (I : Finset ι) {x : Y} (hx : x ∈ U) :
    x ∈ Y.basicOpen (∏ i ∈ I, f i) ↔ ∀ i ∈ I, x ∈ Y.basicOpen (f i) := by sorry
