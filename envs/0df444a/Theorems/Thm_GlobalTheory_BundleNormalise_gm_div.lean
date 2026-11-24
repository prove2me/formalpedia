-- Prove2me | Theorems.Thm_GlobalTheory_BundleNormalise_gm_div
-- name    : GlobalTheory.BundleNormalise.gm_div
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:04:32.168908+00:00
-- url     : https://prove2.me/theorems/3ff8db8f-36ef-48ef-a9b6-beac4355cf8f
-- title:
--   Bundle Normalise: gm div
-- statement:
--   The Bundle Normalise construction uses the gm div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPartialBundleIsoNormalised.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPartialBundleIsoNormalised.lean#L26-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalised
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div

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
noncomputable section
open GlobalTheory GlobalTheory.BundleNormalise
open GlobalTheory.RigidTriv
variable {X Y : Scheme.{0}}

theorem GlobalTheory.BundleNormalise.gm_div {M M' : LB X} (f : Y ⟶ X) (y : Y) (a a' : M.ι) (b b' : M'.ι)
    (hm : f y ∈ M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) :
    gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) ((LB.div M M').g (a, b) (a', b')) =
      gm f y _ (M.g a a') * (gm f y _ (M'.g b b'))⁻¹ := by sorry
