-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_sec_extend
-- name    : GlobalTheory.SecAff.sec_extend
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:09.876255+00:00
-- url     : https://prove2.me/theorems/f82fd54a-6c61-41b9-97d3-3da44e7c0c53
-- title:
--   Sec Aff: sec extend
-- statement:
--   The Sec Aff construction uses the sec extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L179-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L179-L260

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

theorem GlobalTheory.SecAff.sec_extend [CompactSpace X] [QuasiSeparatedSpace X] (φ : X' ⟶ X) [IsOpenImmersion φ]
    (f : Γ(X, ⊤)) (hφ : φ.opensRange = X.basicOpen f) (M : LB X) (hM : M.IsLB)
    (U' : M.ι → X'.Opens) (h : ∀ j, U' j ≤ φ ⁻¹ᵁ M.U j) (h' : ∀ j, φ ⁻¹ᵁ M.U j ≤ U' j)
    (t : ∀ j, Γ(X', U' j))
    (ht : ∀ i j, rs (inf_le_left : U' i ⊓ U' j ≤ U' i) (t i) =
      pa φ (le_pre_inf (inf_le_left.trans (h i)) (inf_le_right.trans (h j)))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) *
        rs (inf_le_right : U' i ⊓ U' j ≤ U' j) (t j)) :
    ∃ (N : ℕ) (s : LB.Sec M), ∀ j, pa φ (h j) (s.f j) = pa φ (le_pre_top φ) f ^ N * t j := by sorry
