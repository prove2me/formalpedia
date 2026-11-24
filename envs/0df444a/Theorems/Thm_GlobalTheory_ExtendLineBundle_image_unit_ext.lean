-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_image_unit_ext
-- name    : GlobalTheory.ExtendLineBundle.image_unit_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:18:33.431278+00:00
-- url     : https://prove2.me/theorems/1c5eff51-9da3-493a-a420-02980a6980d0
-- title:
--   Extend Line Bundle: image unit ext
-- statement:
--   The Extend Line Bundle construction uses the image unit ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L305-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L305-L307

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

theorem GlobalTheory.ExtendLineBundle.image_unit_ext {V : Y.Opens} {a b : Γ(Y, V)ˣ}
    (h : genericPoint X ∈ j ''ᵁ V → imageVal j V a = imageVal j V b) : a = b := by sorry
