-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_pullHO2_surjective_of_wedge
-- name    : GlobalTheory.AbCoh.pullHO2_surjective_of_wedge
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:27:01.465914+00:00
-- url     : https://prove2.me/theorems/9876595a-b93b-42b3-8054-48d987f10df0
-- title:
--   Ab Coh: pull HO2 surjective of wedge
-- statement:
--   The Ab Coh construction uses the pull HO2 surjective of wedge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectivePullHO2OfPullHO1.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectivePullHO2OfPullHO1.lean#L14-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullCupOfBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectivePullHO2OfPullHO1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.pullHO2_surjective_of_wedge : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ),
    Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by sorry
