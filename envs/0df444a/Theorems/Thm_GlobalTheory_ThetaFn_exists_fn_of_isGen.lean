-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_exists_fn_of_isGen
-- name    : GlobalTheory.ThetaFn.exists_fn_of_isGen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:31.463803+00:00
-- url     : https://prove2.me/theorems/6a0f7d11-5e11-4651-a399-b1529bbcfc93
-- title:
--   Theta Fn: exists fn of is Gen
-- statement:
--   The Theta Fn construction uses the exists fn of is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L54-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L54-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}

theorem GlobalTheory.ThetaFn.exists_fn_of_isGen (hL : L.IsLB) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hd : Differentiable ℂ Φ) (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
        r z = valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          u.fr (j 1) (Φ z) ^ b * u.fr (j 0) z ^ (-a) := by sorry
