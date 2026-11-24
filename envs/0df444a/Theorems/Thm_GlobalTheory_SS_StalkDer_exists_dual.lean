-- Prove2me | Theorems.Thm_GlobalTheory_SS_StalkDer_exists_dual
-- name    : GlobalTheory.SS.StalkDer.exists_dual
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:36:56.8498+00:00
-- url     : https://prove2.me/theorems/da8b5b55-d8c1-4b0f-82c0-87c5febc33d5
-- title:
--   Stalk Der: exists dual
-- statement:
--   The Stalk Der construction uses the exists dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L96-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L96-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}

theorem GlobalTheory.SS.StalkDer.exists_dual {Y : Over (Sp K)} (p : P ⟶ X.left) (q : P ⟶ Y.left)
    (H : IsPullback p q X.hom Y.hom) (D : VF X) (E : VF Y) (z : P) :
    ∃ Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z), (∀ a, (Φ a).fst = a) ∧
      (∀ V hz u, Φ (gm p z V hz u) = gmDual D p z V hz u) ∧
      ∀ V hz u, Φ (gm q z V hz u) = gmDual E q z V hz u := by sorry
