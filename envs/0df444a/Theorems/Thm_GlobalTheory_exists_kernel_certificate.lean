-- Prove2me | Theorems.Thm_GlobalTheory_exists_kernel_certificate
-- name    : GlobalTheory.exists_kernel_certificate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:23.319503+00:00
-- url     : https://prove2.me/theorems/c60debf5-77d7-4e09-b476-37ea6476e4ae
-- title:
--   Global Theory: exists kernel certificate
-- statement:
--   The Global Theory construction uses the exists kernel certificate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsMulEqSmulOneOfMulVecInjective.lean#L55-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsMulEqSmulOneOfMulVecInjective.lean#L55-L156

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsMulEqSmulOneOfMulVecInjective
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
open GlobalTheory

theorem GlobalTheory.exists_kernel_certificate {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    (D₀ : Matrix b a R) (D₁ : Matrix c b R) (h0 : D₁ * D₀ = 0)
    (hex : ∀ w : b → K, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) :
    ∃ (r : R) (n : ℕ) (B : Matrix a (Fin n) R) (C : Matrix (Fin n) a R) (H : Matrix a b R),
      g r ≠ 0 ∧ D₀ * B = 0 ∧ C * B = r • (1 : Matrix (Fin n) (Fin n) R) ∧
        B * C + H * D₀ = r • (1 : Matrix a a R) := by sorry
