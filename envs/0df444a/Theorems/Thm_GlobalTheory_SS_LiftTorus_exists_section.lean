-- Prove2me | Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_section
-- name    : GlobalTheory.SS.LiftTorus.exists_section
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:35.671559+00:00
-- url     : https://prove2.me/theorems/5650c148-1435-4df0-a22b-490b24a787fb
-- title:
--   Lift Torus: exists section
-- statement:
--   The Lift Torus construction uses the exists section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftOneParameterQuotientTorus.lean#L175-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftOneParameterQuotientTorus.lean#L175-L198

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068

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

theorem GlobalTheory.SS.LiftTorus.exists_section {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G B : Over S}
    [GrpObj G] [GrpObj B] {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
    [Flat q.left] [Surjective q.left] [IsAffineHom q.left] [IsAffine B.left]
    [Subsingleton (CommRing.Pic Γ(B.left, ⊤))]
    (hi : IsPullback i (toUnit _) q η[B]) : ∃ s : B ⟶ G, s ≫ q = 𝟙 B := by sorry
