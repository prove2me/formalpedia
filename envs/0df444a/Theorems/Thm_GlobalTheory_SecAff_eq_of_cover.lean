-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_eq_of_cover
-- name    : GlobalTheory.SecAff.eq_of_cover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:06.87459+00:00
-- url     : https://prove2.me/theorems/9019a5e4-0d36-46bd-ae22-063908cdc382
-- title:
--   Sec Aff: eq of cover
-- statement:
--   The Sec Aff construction uses the eq of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L72-L74

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

theorem GlobalTheory.SecAff.eq_of_cover {κ : Type} {U : X.Opens} (W : κ → X.Opens) (hW : ∀ a, W a ≤ U)
    (hc : U ≤ ⨆ a, W a) (x y : Γ(X, U)) (h : ∀ a, rs (hW a) x = rs (hW a) y) : x = y := by sorry
