-- Prove2me | Theorems.Thm_GlobalTheory_PartialBundleGlue_pull_isGen_of
-- name    : GlobalTheory.PartialBundleGlue.pull_isGen_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:01.188596+00:00
-- url     : https://prove2.me/theorems/4099d04a-ae03-480e-bcd3-fb94c54be737
-- title:
--   Partial Bundle Glue: pull is Gen of
-- statement:
--   The Partial Bundle Glue construction uses the pull is Gen of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlueRigidifiedPartialLineBundles.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlueRigidifiedPartialLineBundles.lean#L41-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalisedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGlueRigidifiedPartialLineBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.PartialBundleGlue

theorem GlobalTheory.PartialBundleGlue.pull_isGen_of {X S : Scheme.{0}} {L : LB X} {e : S ⟶ X} (r : (L.pull e).Gen)
    (h : ∀ (x : S) (a b : L.ι), e x ∈ L.U a → e x ∈ L.U b →
      gm (𝟙 S) x ((L.pull e).U fun _ => a) (r.s fun _ => a) =
        gm e x (L.U a ⊓ L.U b) (L.g a b) * gm (𝟙 S) x ((L.pull e).U fun _ => b) (r.s fun _ => b)) :
    r.IsGen := by sorry
