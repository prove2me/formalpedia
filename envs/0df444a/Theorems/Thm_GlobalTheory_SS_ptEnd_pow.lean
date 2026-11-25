-- Prove2me | Theorems.Thm_GlobalTheory_SS_ptEnd_pow
-- name    : GlobalTheory.SS.ptEnd_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:37:14.438175+00:00
-- url     : https://prove2.me/theorems/baa9b25c-e3e4-406b-948b-e9fc6905965c
-- title:
--   SS: pt End pow
-- statement:
--   The SS construction uses the pt End pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPolyNormSqRoots.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPolyNormSqRoots.lean#L109-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVectorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPolyNormSqRoots
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
open Polynomial
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem GlobalTheory.SS.ptEnd_pow (F : End B) (hF : IsMonHom (show B ⟶ B from F)) {Z : Over S} (x : Z ⟶ B) (n : ℕ) :
    (ptEnd F hF Z ^ n) (Additive.ofMul x) = Additive.ofMul (x ≫ (show B ⟶ B from F ^ n)) := by sorry
