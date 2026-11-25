-- Prove2me | Theorems.Thm_GlobalTheory_mem_finset_biInf_opens_iff
-- name    : GlobalTheory.mem_finset_biInf_opens_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:47:43.8049+00:00
-- url     : https://prove2.me/theorems/aec0ab12-c3bc-49c2-a9de-f242dad8672d
-- title:
--   Global Theory: mem finset bi Inf opens iff
-- statement:
--   The Global Theory construction uses the mem finset bi Inf opens iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L32-L39

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

theorem GlobalTheory.mem_finset_biInf_opens_iff {Y : Scheme.{0}} {ι : Type} (D : ι → Y.Opens) (I : Finset ι)
    {x : Y} : x ∈ (⨅ i ∈ I, D i) ↔ ∀ i ∈ I, x ∈ D i := by sorry
