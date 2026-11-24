-- Prove2me | Theorems.Thm_GlobalTheory_Published_FormalAlgebraisation_Morphisms_existsUnique_thick
-- name    : GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:56:55.945563+00:00
-- url     : https://prove2.me/theorems/9e21f727-eb82-4fe4-af9e-a52a39f0ce23
-- title:
--   Morphisms: exists Unique thick
-- statement:
--   The Morphisms construction uses the exists Unique thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/FormalAlgebraisation.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/FormalAlgebraisation.lean#L50-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.FormalAlgebraisation
variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}

theorem GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick (H : Morphisms) (hI : IsAdicComplete I R)
    (X Z : Over (Spec (CommRingCat.of R))) [hX : IsProper X.hom] [hZ : IsProper Z.hom]
    (f : ∀ e, (thickObj R I e X).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst X.hom (thick R I e) ≫ X.hom)
    (hc : ∀ e, thickMap R I e X ≫ f (e + 1) = f e) :
    ∃! g : X ⟶ Z, ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = f e := by sorry
