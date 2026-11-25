-- Prove2me | Theorems.Thm_GlobalTheory_exists_prod_sec_nonzeroLocus
-- name    : GlobalTheory.exists_prod_sec_nonzeroLocus
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:52:50.022702+00:00
-- url     : https://prove2.me/theorems/49eba00c-d653-430a-86cc-3f1db5ebc4f7
-- title:
--   Global Theory: exists prod sec nonzero Locus
-- statement:
--   The Global Theory construction uses the exists prod sec nonzero Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemNonzeroLocusIffMemBasicOpenChart.lean#L41-L59

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

theorem GlobalTheory.exists_prod_sec_nonzeroLocus : ∀ (Y : Scheme.{0}) (H : LB Y) (ι : Type) (s : ι → LB.Sec H) (I : Finset ι), H.IsLB → ∃ σ : LB.Sec (pw H (I.card : ℤ)), (∀ l : H.ι, σ.f l = ∏ i ∈ I, (s i).f l) ∧ nonzeroLocus σ = ⨅ i ∈ I, nonzeroLocus (s i) := by sorry
