-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeGen_mem_range_spec
-- name    : GlobalTheory.AbLaw.CubeGen.mem_range_spec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:50:55.178646+00:00
-- url     : https://prove2.me/theorems/497d5617-4015-4291-92b6-e641f289364b
-- title:
--   Cube Gen: mem range spec
-- statement:
--   The Cube Gen construction uses the mem range spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L177-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L177-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem GlobalTheory.AbLaw.CubeGen.mem_range_spec {R F : Type} [CommRing R] [Field F] (g : R →+* F) (x : PrimeSpectrum R) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom g)) ↔ RingHom.ker g = x.asIdeal := by sorry
