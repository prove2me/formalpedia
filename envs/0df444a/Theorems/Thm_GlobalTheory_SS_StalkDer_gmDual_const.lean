-- Prove2me | Theorems.Thm_GlobalTheory_SS_StalkDer_gmDual_const
-- name    : GlobalTheory.SS.StalkDer.gmDual_const
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:36:07.566229+00:00
-- url     : https://prove2.me/theorems/6413bef9-6657-4fd4-8749-8f1171ee8f96
-- title:
--   Stalk Der: gm Dual const
-- statement:
--   The Stalk Der construction uses the gm Dual const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L76-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean#L76-L94

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

theorem GlobalTheory.SS.StalkDer.gmDual_const (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V)
    (c : Γ(Sp K, ⊤)) :
    gmDual D f z V hz ((X.hom.appLE ⊤ V le_top).hom c) =
      TrivSqZeroExt.inl ((P.presheaf.germ ⊤ z trivial).hom (((f ≫ X.hom).appLE ⊤ ⊤ le_top).hom c)) := by sorry
