-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_fun_kill
-- name    : GlobalTheory.SecAff.fun_kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:11.685322+00:00
-- url     : https://prove2.me/theorems/920e49c6-2551-44d8-b8a4-cb25e7b65fd6
-- title:
--   Sec Aff: fun kill
-- statement:
--   The Sec Aff construction uses the fun kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L101-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L101-L114

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

theorem GlobalTheory.SecAff.fun_kill (φ : X' ⟶ X) [IsOpenImmersion φ] (f : Γ(X, ⊤))
    (hφ : φ.opensRange = X.basicOpen f) {W : X.Opens} (hW : IsCompact (W : Set X)) {W' : X'.Opens}
    (h : W' ≤ φ ⁻¹ᵁ W) (h' : φ ⁻¹ᵁ W ≤ W') (x : Γ(X, W)) (hx : pa φ h x = 0) :
    ∃ N : ℕ, rs (le_top : W ≤ ⊤) f ^ N * x = 0 := by sorry
