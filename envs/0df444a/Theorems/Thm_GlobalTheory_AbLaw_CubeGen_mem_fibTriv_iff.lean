-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeGen_mem_fibTriv_iff
-- name    : GlobalTheory.AbLaw.CubeGen.mem_fibTriv_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:50:53.114796+00:00
-- url     : https://prove2.me/theorems/dbf11a95-3a45-49c7-b063-65b2616b041d
-- title:
--   Cube Gen: mem fib Triv iff
-- statement:
--   The Cube Gen construction uses the mem fib Triv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L187-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L187-L212

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

theorem GlobalTheory.AbLaw.CubeGen.mem_fibTriv_iff {p : Y ⟶ T} {R : Type} [CommRing R] {j : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion j]
    {q : W ⟶ Y} {f : W ⟶ Spec (CommRingCat.of R)} (H : IsPullback q f p j) (x : PrimeSpectrum R) :
    j x ∈ fibTriv L φ ε p ↔ ∃ (F : Type) (_ : Field F) (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W)
      (f' : Z ⟶ Spec (CommRingCat.of F)), RingHom.ker g = x.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧
      Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) := by sorry
