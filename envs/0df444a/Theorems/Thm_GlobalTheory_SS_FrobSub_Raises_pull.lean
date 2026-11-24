-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobSub_Raises_pull
-- name    : GlobalTheory.SS.FrobSub.Raises.pull
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:33:32.949745+00:00
-- url     : https://prove2.me/theorems/bd1dcfaa-9603-4e17-ab38-9703a6be6b16
-- title:
--   Raises: pull
-- statement:
--   The Raises construction uses the pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L35-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobSub

theorem GlobalTheory.SS.FrobSub.Raises.pull {X Y : Scheme.{0}} (ν : Y ⟶ X) {φ : X ⟶ X} {ψ : Y ⟶ Y} (hc : ψ ≫ ν = ν ≫ φ) {a : ℕ}
    {V : X.Opens} {g : Γ(X, V)} (h : Raises φ a V g) : Raises ψ a (ν ⁻¹ᵁ V) ((ν.app V).hom g) := by sorry
