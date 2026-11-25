-- Prove2me | Theorems.Thm_GlobalTheory_tate_basis_matrix
-- name    : GlobalTheory.tate_basis_matrix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:02.184012+00:00
-- url     : https://prove2.me/theorems/831cc060-19e8-53b6-9b14-b5e4772da3a3
-- title:
--   Global Theory: tate basis matrix
-- statement:
--   The Global Theory construction uses the tate basis matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TateBasisMatrix.lean#L132-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TateBasisMatrix.lean#L132-L190

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.tate_basis_matrix :
    (∀ (p : ℕ) [Fact p.Prime] (κ Γ : Type) [Fintype κ] [DecidableEq κ] [AddCommGroup Γ] (τ : κ → ℕ → Γ),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) →
    (∀ n (x : Γ), (p ^ (n + 1)) • x = 0 → ∃! t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n) ∧
    ∃ ρ : AddMonoid.End Γ →+* Matrix κ κ ℤ_[p], ∀ (f : AddMonoid.End Γ) j n,
      f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ f k j)).val • τ k n) := by sorry
