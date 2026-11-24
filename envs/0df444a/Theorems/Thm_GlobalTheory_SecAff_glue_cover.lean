-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_glue_cover
-- name    : GlobalTheory.SecAff.glue_cover
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:20.452129+00:00
-- url     : https://prove2.me/theorems/3169a4f0-cb0f-4201-868c-4897ed224851
-- title:
--   Sec Aff: glue cover
-- statement:
--   The Sec Aff construction uses the glue cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L76-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}

theorem GlobalTheory.SecAff.glue_cover {κ : Type} {U : X.Opens} (W : κ → X.Opens) (hW : ∀ a, W a ≤ U)
    (hc : U ≤ ⨆ a, W a) (x : ∀ a, Γ(X, W a))
    (h : ∀ a b, rs (inf_le_left : W a ⊓ W b ≤ W a) (x a) = rs (inf_le_right : W a ⊓ W b ≤ W b) (x b)) :
    ∃ y : Γ(X, U), ∀ a, rs (hW a) y = x a := by sorry
