-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_sec_kill
-- name    : GlobalTheory.SecAff.sec_kill
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:23.101978+00:00
-- url     : https://prove2.me/theorems/a171b8f9-78a7-4224-bfab-ff5020130bcc
-- title:
--   Sec Aff: sec kill
-- statement:
--   The Sec Aff construction uses the sec kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L157-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L157-L177

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

theorem GlobalTheory.SecAff.sec_kill [CompactSpace X] (φ : X' ⟶ X) [IsOpenImmersion φ] (f : Γ(X, ⊤))
    (hφ : φ.opensRange = X.basicOpen f) (M : LB X) (hM : M.IsLB) (U' : M.ι → X'.Opens)
    (h : ∀ j, U' j ≤ φ ⁻¹ᵁ M.U j) (h' : ∀ j, φ ⁻¹ᵁ M.U j ≤ U' j) (s : LB.Sec M)
    (hs : ∀ j, pa φ (h j) (s.f j) = 0) :
    ∃ N : ℕ, ∀ j, rs (le_top : M.U j ≤ ⊤) f ^ N * s.f j = 0 := by sorry
