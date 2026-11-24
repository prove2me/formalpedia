-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_pull_analytic_at
-- name    : GlobalTheory.ThetaFn.pull_analytic_at
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:38.882241+00:00
-- url     : https://prove2.me/theorems/0b2be6e8-6e11-44b1-a44c-4683954feb55
-- title:
--   Theta Fn: pull analytic at
-- statement:
--   The Theta Fn construction uses the pull analytic at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L240-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L240-L264

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

theorem GlobalTheory.ThetaFn.pull_analytic_at (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} (hm : ψ ≫ snd T A = m)
    {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (hψ : ∀ z, exAt u p z ≫ ψ.left = exAt u p (Φ z)) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    (∀ z w, (b : ℂ) * hermForm Hm (Φ z) (Φ w) = a * hermForm Hm z w) ∧
    ∃ c : ℂ, c ≠ 0 ∧ IsPullConst u p Φ a b α c ∧
      (∀ (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) (θ θ' : (Fin g → ℂ) → ℂ),
        IsTwistPull A L ψ m hm a b α s s' → IsFnAt u p b s θ → IsFnAt u p a s' θ' →
          ∀ z, θ' z = c * θ (Φ z)) ∧
      ∀ rig : LB.Gen (L.pull (eSec A)), u.IsRig rig →
        (∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
          valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
              valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
            c * valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) ∧
        ((∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
          valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
              valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
            valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) →
          c = 1) := by sorry
