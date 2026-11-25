-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_cechLB_pull_iso_of_isOpenImmersion
-- name    : GlobalTheory.AbLaw.cechLB_pull_iso_of_isOpenImmersion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:13.445868+00:00
-- url     : https://prove2.me/theorems/3d54d3aa-e4b0-4ba7-b732-d0c25ac8897c
-- title:
--   Ab Law: cech LB pull iso of is Open Immersion
-- statement:
--   The Ab Law construction uses the cech LB pull iso of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechLBPullIsoOfIsOpenImmersion.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechLBPullIsoOfIsOpenImmersion.lean#L46-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBPullIsoOfIsOpenImmersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw

theorem GlobalTheory.AbLaw.cechLB_pull_iso_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (Y' : Scheme.{0}) (e : Y' ⟶ Y) [IsOpenImmersion e] (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → (∀ i, D i ≤ e.opensRange) → Nonempty (cechLB (e ≫ f) (M.pull e) (fun i => e ⁻¹ᵁ D i) ≅ cechLB f M D) := by sorry
