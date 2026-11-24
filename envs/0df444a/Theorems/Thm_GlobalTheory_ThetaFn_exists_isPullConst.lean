-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_exists_isPullConst
-- name    : GlobalTheory.ThetaFn.exists_isPullConst
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:28:25.755849+00:00
-- url     : https://prove2.me/theorems/8e88803a-e53a-4aee-94cd-334312a3cd0b
-- title:
--   Theta Fn: exists is Pull Const
-- statement:
--   The Theta Fn construction uses the exists is Pull Const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L103-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L103-L160

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

theorem GlobalTheory.ThetaFn.exists_isPullConst (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    (∀ z w, (b : ℂ) * hermForm Hm (Φ z) (Φ w) = a * hermForm Hm z w) ∧
      (∀ l : u.Λ, χ ⟨Φ l, map_mem_period hΦ l.2⟩ ^ b = χ l ^ a) ∧
      ∃ c : ℂ, c ≠ 0 ∧ IsPullConst u p Φ a b α c := by sorry
