-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_imageUnit_res
-- name    : GlobalTheory.ExtendLineBundle.imageUnit_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:42.609849+00:00
-- url     : https://prove2.me/theorems/4a15aa75-cdf6-457a-9538-dd640e3b2f39
-- title:
--   Extend Line Bundle: image Unit res
-- statement:
--   The Extend Line Bundle construction uses the image Unit res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L283-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L283-L285

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
variable (j : Y ⟶ X) [IsOpenImmersion j]
omit [IsIntegral X]

theorem GlobalTheory.ExtendLineBundle.imageUnit_res {U V : Y.Opens} (hle : V ≤ U) (a : Γ(Y, U)ˣ) :
    imageUnit j V (res hle a) = res (j.image_mono hle) (imageUnit j U a) := by sorry
