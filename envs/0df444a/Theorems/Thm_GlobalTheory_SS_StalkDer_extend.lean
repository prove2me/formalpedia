-- Prove2me | Theorems.Thm_GlobalTheory_SS_StalkDer_extend
-- name    : GlobalTheory.SS.StalkDer.extend
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:37:20.046803+00:00
-- url     : https://prove2.me/theorems/444cc8a6-91db-4b23-834f-8f04066b42db
-- title:
--   Stalk Der: extend
-- statement:
--   The Stalk Der construction uses the extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L58-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L58-L74

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

theorem GlobalTheory.SS.StalkDer.extend (D : VF X) (f : P ⟶ X.left) (z : P)
    (Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z)) (V₀ : X.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hz₀ : z ∈ f ⁻¹ᵁ V₀)
    (H : ∀ u, Φ (gm f z V₀ hz₀ u) = gmDual D f z V₀ hz₀ u)
    (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) (u : Γ(X.left, V)) :
    Φ (gm f z V hz u) = gmDual D f z V hz u := by sorry
