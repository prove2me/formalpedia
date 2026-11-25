-- Prove2me | Theorems.Thm_GlobalTheory_SS_aeval_intertwine
-- name    : GlobalTheory.SS.aeval_intertwine
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:04.680031+00:00
-- url     : https://prove2.me/theorems/6c43816d-7441-4369-98f9-7c669529437f
-- title:
--   SS: aeval intertwine
-- statement:
--   The SS construction uses the aeval intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPolyNormSqRoots.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPolyNormSqRoots.lean#L58-L66

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

theorem GlobalTheory.SS.aeval_intertwine {M N : Type} [AddCommGroup M] [AddCommGroup N] (π : M →ₗ[ℤ] N) (S : Module.End ℤ M)
    (T : Module.End ℤ N) (h : ∀ x, T (π x) = π (S x)) (p : ℤ[X]) : ∀ x, aeval T p (π x) = π (aeval S p x) := by sorry
