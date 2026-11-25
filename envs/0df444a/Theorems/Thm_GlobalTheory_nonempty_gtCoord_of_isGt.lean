-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_gtCoord_of_isGt
-- name    : GlobalTheory.nonempty_gtCoord_of_isGt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:53.67773+00:00
-- url     : https://prove2.me/theorems/6ed4c913-b5e3-4302-9895-53576df1d2e5
-- title:
--   Global Theory: nonempty gt Coord of is Gt
-- statement:
--   The Global Theory construction uses the nonempty gt Coord of is Gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L486-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L486-L574

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open WeightGen

theorem GlobalTheory.nonempty_gtCoord_of_isGt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : E.B ≅ thickObj R I e D.P.A) (xe : D.X ≃+ E.X), IsMonHom β.hom → (∀ χ : D.X, ∃ w : LB.Iso (E.O (xe χ)).L (LB.LinComb D.P.L (fun k => ((Over.map (thick R I e)).map β.hom ≫ D.prBe I e).left ≫ D.Oφ (𝟙 _) χ k) Oε), w.IsGen) → E.IsGt (thickObj R I e G) → Nonempty (GtCoord I D e G) := by sorry
