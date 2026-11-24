-- Prove2me | Theorems.Thm_GlobalTheory_SS_GenProj_eq_of_generic
-- name    : GlobalTheory.SS.GenProj.eq_of_generic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:33:52.145219+00:00
-- url     : https://prove2.me/theorems/1c0d5833-8a29-49e4-8a4c-64f900607bb6
-- title:
--   Gen Proj: eq of generic
-- statement:
--   The Gen Proj construction uses the eq of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GenericIsomorphismProductModels.lean#L32-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GenericIsomorphismProductModels.lean#L32-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj

theorem GlobalTheory.SS.GenProj.eq_of_generic {S E U X X' A : Scheme.{0}} (i : E ⟶ S) [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (s : X ⟶ S) (s' : X' ⟶ S) [Flat s] [IsSeparated s'] (p : U ⟶ X) (q : U ⟶ X') [Flat p]
    (hs : p ≫ s = q ≫ s') (j : A ⟶ X) [Mono j] (j' : A ⟶ X')
    (H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U) (t : Z ⟶ E), a ≫ p ≫ s = t ≫ i → ∃ c : Z ⟶ A, c ≫ j = a ≫ p ∧ c ≫ j' = a ≫ q)
    {Z : Scheme.{0}} (a b : Z ⟶ U) (hab : a ≫ p = b ≫ p) : a ≫ q = b ≫ q := by sorry
