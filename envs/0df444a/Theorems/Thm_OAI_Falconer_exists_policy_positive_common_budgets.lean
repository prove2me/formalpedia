-- Prove2me | Theorems.Thm_OAI_Falconer_exists_policy_positive_common_budgets
-- name    : OAI.Falconer.exists_policy_positive_common_budgets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:49:37.241895+00:00
-- url     : https://prove2.me/theorems/a6d44a67-a8a8-426a-8a53-bfee4e5111db
-- title:
--   OAI.Falconer.exists_policy_positive_common_budgets: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_policy_positive_common_budgets` of [lean/OAI/MeasureTheory/Falconer/Estimates/PolicyCommonBudgets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/PolicyCommonBudgets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped SchwartzMap`, `open PlanarFalconer (policyDepth)`):
--
--   ```lean
--   theorem exists_policy_positive_common_budgets
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (m : ℕ) {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
--       {J : ℕ} (hJ : 0 < J) (T : ℝ)
--       (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
--       (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
--       (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
--       {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
--       (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
--       ∃ K : ℕ, minJet ≤ K ∧ ∀ minOrder : ℕ, ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
--         PolicyGraphBound m K L J lam σ ((ε/2)/2) ((T+ε/2)+1+(ε/2)/2) Z N₀ Ψ ∧
--         ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
--         P.i+1 ≤ P.J → P.a₀ = P.a → P.t₀ = P.t → P.a+100*P.q < P.t →
--         P.σ*(P.N:ℝ) ≤ P.q →
--         2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t →
--         (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
--           dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
--         125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
--           ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
--         ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
--           2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
--         ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
--         ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) ≤ M →
--         (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
--           ((2:ℝ)^P.N)^ε*(positiveCollisionCount w₀ P.Q P.ρ
--             (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M) →
--         (∀ v, ∀ hv : v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
--           ∀ p, p = policyDepth P.policy P.N P.q P.a P.t → ∀ hap : P.a ≤ p,
--           ∀ row, ∀ hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
--             (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
--           P.directWeight p lam σ ε *
--             ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child p hap row hrow).envelope K L Ψ ≤ M) →
--         P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor` and `OAI.PlanarFalconer.policyDepth` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.PolicyGraphBound`, `OAI.Falconer.PolicyJetData`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorMaskRadius`, `OAI.Falconer.positiveCollisionCount`, `OAI.Falconer.DyadicCube.center`, `OAI.Falconer.DyadicCube.descendant`, `OAI.Falconer.DyadicCube.occupiedPaths`, `OAI.Falconer.DyadicCube`, `OAI.Falconer.PolicyJetData.atFrequency`, `OAI.Falconer.PolicyJetData.child`, `OAI.Falconer.PolicyJetData.directWeight`, `OAI.Falconer.PolicyJetData.envelope`, `OAI.Falconer.PolicyJetData.list` and `OAI.Falconer.PolicyJetData.positiveCount` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface` and `OAI.Falconer.PublishedQuadraticStationary` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.exists_policy_recursion_bounds` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/PolicyCommonBudgets.lean (declaration OAI.Falconer.exists_policy_positive_common_budgets)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (policyDepth)

theorem exists_policy_positive_common_budgets
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ K : ℕ, minJet ≤ K ∧ ∀ minOrder : ℕ, ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      PolicyGraphBound m K L J lam σ ((ε/2)/2) ((T+ε/2)+1+(ε/2)/2) Z N₀ Ψ ∧
      ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
      P.i+1 ≤ P.J → P.a₀ = P.a → P.t₀ = P.t → P.a+100*P.q < P.t →
      P.σ*(P.N:ℝ) ≤ P.q →
      2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) ≤ M →
      (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        ((2:ℝ)^P.N)^ε*(positiveCollisionCount w₀ P.Q P.ρ
          (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M) →
      (∀ v, ∀ hv : v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        ∀ p, p = policyDepth P.policy P.N P.q P.a P.t → ∀ hap : P.a ≤ p,
        ∀ row, ∀ hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
        P.directWeight p lam σ ε *
          ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child p hap row hrow).envelope K L Ψ ≤ M) →
      P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T) := by
  sorry

end Falconer

end OAI
end
