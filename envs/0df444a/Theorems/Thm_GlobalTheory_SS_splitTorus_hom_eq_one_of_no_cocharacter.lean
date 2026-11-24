-- Prove2me | Theorems.Thm_GlobalTheory_SS_splitTorus_hom_eq_one_of_no_cocharacter
-- name    : GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:49.387994+00:00
-- url     : https://prove2.me/theorems/7d1cea10-7401-4388-af37-2b5abb00d816
-- title:
--   SS: split Torus hom eq one of no cocharacter
-- statement:
--   The SS construction uses the split Torus hom eq one of no cocharacter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusHomEqOneOfNoCocharacter.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusHomEqOneOfNoCocharacter.lean#L15-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusHomEqOneOfNoCocharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) →
      ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by sorry
