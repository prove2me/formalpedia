-- Prove2me | Theorems.Thm_GlobalTheory_GlueLineBundle_gm_glue_g
-- name    : GlobalTheory.GlueLineBundle.gm_glue_g
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:05.172297+00:00
-- url     : https://prove2.me/theorems/c73b2059-de7e-4f5c-ae77-62a72660207a
-- title:
--   Glue Line Bundle: gm glue g
-- statement:
--   The Glue Line Bundle construction uses the gm glue g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L95-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)

theorem GlobalTheory.GlueLineBundle.gm_glue_g (a : A) {Y : Scheme.{0}} (f : Y ⟶ (V a).toScheme) (y : Y) (i k : (M a).ι)
    (hi : f y ∈ (M a).U i) (hk : f y ∈ (M a).U k) :
    gm (f ≫ (V a).ι) y _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by sorry
