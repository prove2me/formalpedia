-- Prove2me | Theorems.Thm_GlobalTheory_SS_compat_of_isoAt_closure
-- name    : GlobalTheory.SS.compat_of_isoAt_closure
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:10:47.911398+00:00
-- url     : https://prove2.me/theorems/e46d3ca8-351a-4836-8b57-c54638ed13a7
-- title:
--   SS: compat of iso At closure
-- statement:
--   The SS construction uses the compat of iso At closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenImmersionOfSections.lean#L85-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenImmersionOfSections.lean#L85-L172

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
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
open CompatCrit

theorem GlobalTheory.SS.compat_of_isoAt_closure : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [IsIntegral A.left] (M N : Model R A) (δ : A.left ⟶ (M.Y ⊗ N.Y).left), δ ≫ (fst M.Y N.Y).left = M.j → δ ≫ (snd M.Y N.Y).left = N.j → (∀ z ∈ closure (Set.range δ), IsClosed {z} → (fst M.Y N.Y).left z ∈ M.sp → IsoAt M N (𝟙 A) ((fst M.Y N.Y).left z)) → Compat M N := by sorry
