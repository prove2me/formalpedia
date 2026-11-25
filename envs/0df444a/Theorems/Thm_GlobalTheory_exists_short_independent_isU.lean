-- Prove2me | Theorems.Thm_GlobalTheory_exists_short_independent_isU
-- name    : GlobalTheory.exists_short_independent_isU
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:54.345964+00:00
-- url     : https://prove2.me/theorems/e7298145-5898-4686-b364-91470756cc3e
-- title:
--   Global Theory: exists short independent is U
-- statement:
--   The Global Theory construction uses the exists short independent is U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsShortIndependentIsU.lean#L35-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsShortIndependentIsU.lean#L35-L147

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIndependentIsU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
open GlobalTheory
noncomputable section

theorem GlobalTheory.exists_short_independent_isU :
    (∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam → (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 → lam ≤ ‖z‖) → ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam) → (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (a : Vsp X.dim), ((∀ y ∈ X.L, (Hf y a).im = 0) → a = 0) ∧ ((∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) → a ∈ X.L)) → (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)), I ≤ X.L → (∀ x ∈ X.L, x ∈ IR I → x ∈ I) → 0 < X.la1 → ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ (Module.finrank ℝ (IR I) : ℝ) ^ 2 / X.la1) := by sorry
