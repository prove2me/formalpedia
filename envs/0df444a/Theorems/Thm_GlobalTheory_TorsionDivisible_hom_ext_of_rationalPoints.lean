-- Prove2me | Theorems.Thm_GlobalTheory_TorsionDivisible_hom_ext_of_rationalPoints
-- name    : GlobalTheory.TorsionDivisible.hom_ext_of_rationalPoints
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:08.019592+00:00
-- url     : https://prove2.me/theorems/9f6b4ee0-37d6-4084-a160-cb665dac2ebc
-- title:
--   Torsion Divisible: hom ext of rational Points
-- statement:
--   The Torsion Divisible construction uses the hom ext of rational Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AbelianVarietyTorsionFiniteEndomorphismDivisible.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AbelianVarietyTorsionFiniteEndomorphismDivisible.lean#L18-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisible
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
open GlobalTheory GlobalTheory.TorsionDivisible

theorem GlobalTheory.TorsionDivisible.hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by sorry
