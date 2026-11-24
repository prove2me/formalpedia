-- Prove2me | Theorems.Thm_GlobalTheory_TorusToProper_units_family_trivial
-- name    : GlobalTheory.TorusToProper.units_family_trivial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:19.388489+00:00
-- url     : https://prove2.me/theorems/e5a74192-db63-437c-9b24-9101dd972a67
-- title:
--   Torus To Proper: units family trivial
-- statement:
--   The Torus To Proper construction uses the units family trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L69-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L69-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
open PowerSeries

theorem GlobalTheory.TorusToProper.units_family_trivial {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsProper B.hom]
    (Φ : ∀ (R : Type) [CommRing R] [Algebra K R], Rˣ →* (sp K R ⟶ B))
    (hΦ : ∀ (R R' : Type) [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (g : R →ₐ[K] R')
      (x : Rˣ), Φ R' (Units.map (g : R →* R') x) = spm g ≫ Φ R x)
    (L : Type) [Field L] [Algebra K L] (x : Lˣ) : Φ L x = 1 := by sorry
