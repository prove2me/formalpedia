-- Prove2me | Theorems.Thm_GlobalTheory_PartialBundleGlue_iso_isGen_iff
-- name    : GlobalTheory.PartialBundleGlue.iso_isGen_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:57.965532+00:00
-- url     : https://prove2.me/theorems/79939389-3486-4588-9ed3-915f01614211
-- title:
--   Partial Bundle Glue: iso is Gen iff
-- statement:
--   The Partial Bundle Glue construction uses the iso is Gen iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlueRigidifiedPartialLineBundles.lean#L15-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlueRigidifiedPartialLineBundles.lean#L15-L39

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

theorem GlobalTheory.PartialBundleGlue.iso_isGen_iff {X : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) :
    w.IsGen ↔ ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a → x ∈ M.U a' → x ∈ L.U b → x ∈ L.U b' →
      gm (𝟙 X) x (M.U a ⊓ L.U b) (w.s (a, b)) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
          gm (𝟙 X) x (M.U a' ⊓ L.U b') (w.s (a', b')) := by sorry
