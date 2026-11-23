-- Prove2me | Theorems.Thm_GlobalTheory_SS_StalkDer_germ_appLE
-- name    : GlobalTheory.SS.StalkDer.germ_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:11.269007+00:00
-- url     : https://prove2.me/theorems/861b4218-d6b3-4b45-ac35-06b0cf1e9c41
-- title:
--   Stalk Der: germ app LE
-- statement:
--   The Stalk Der construction uses the germ app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L19-L22

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

theorem GlobalTheory.SS.StalkDer.germ_appLE (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (W : P.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (hz : z ∈ W) (u : Γ(X.left, V)) :
    (P.presheaf.germ W z hz).hom ((f.appLE V W h).hom u) = gm f z V (h hz) u := by sorry
