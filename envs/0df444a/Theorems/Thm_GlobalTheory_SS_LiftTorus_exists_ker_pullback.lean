-- Prove2me | Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_ker_pullback
-- name    : GlobalTheory.SS.LiftTorus.exists_ker_pullback
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:36:58.359725+00:00
-- url     : https://prove2.me/theorems/62a2339e-16a3-4c21-b4c1-043bce8d0747
-- title:
--   Lift Torus: exists ker pullback
-- statement:
--   The Lift Torus construction uses the exists ker pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftOneParameterQuotientTorus.lean#L159-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftOneParameterQuotientTorus.lean#L159-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LiftTorus
open GlobalTheory.TorsorUnit

theorem GlobalTheory.SS.LiftTorus.exists_ker_pullback {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {T G B H E : C} [GrpObj T] [GrpObj G] [GrpObj B] [GrpObj H] [GrpObj E] {i : T ⟶ G} {q : G ⟶ B}
    {f : H ⟶ B} {p : E ⟶ G} {r : E ⟶ H} [IsMonHom i] [IsMonHom f] [IsMonHom p] [IsMonHom r]
    (hi : IsPullback i (toUnit _) q η[B]) (h : IsPullback p r q f) :
    ∃ j : T ⟶ E, IsMonHom j ∧ IsPullback j (toUnit _) r η[H] := by sorry
