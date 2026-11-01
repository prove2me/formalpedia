-- Prove2me | Theorems.Thm_OAI_JointDickman_ramare_product_sparse_integral_jd
-- name    : OAI.JointDickman.ramare_product_sparse_integral_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:29:44.959493+00:00
-- url     : https://prove2.me/theorems/25d508e4-73c0-473e-b318-1fb26adde7df
-- title:
--   OAI.JointDickman.ramare_product_sparse_integral_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.ramare_product_sparse_integral` of [lean/OAI/NumberTheory/JointDickman/Amplification/RamareProductIntegral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/RamareProductIntegral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory TwoPointCorrelations`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem ramare_product_sparse_integral_jd (B : ℝ) (hB : 1 ≤ B) :
--       ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
--         ∀ᶠ a : ℝ in atTop, ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
--         1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
--         (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
--         ∀ (E : Set ℝ) (T τ b K : ℝ), MeasurableSet E → 0 ≤ T → 0 ≤ τ →
--         E ⊆ Set.Ioc (-T) T → 2*T ≤ a^B →
--         let Qf := mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
--           (fun p => -Real.log (p:ℝ))
--         (∀ U : Finset ℝ, (∀ t ∈ U, t ∈ E) →
--           (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
--           (U.card:ℝ) ≤ K ∧ ((U.filter (fun t => τ < ‖Qf t‖)).card:ℝ) ≤ a^γ) →
--         (∀ t ∈ E, τ < ‖Qf t‖ → ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
--         (∫ t in E, ‖Qf t*mrtCofactorPolynomial P F N a t‖^2) ≤
--           2*(τ^2*(48000*(2*(1+Real.log (2*T+1))+K*Real.sqrt (2*T)*a/N))+
--             b^2*(C/(Real.log a)^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwoPointCorrelations.mrtExponentialPolynomial` (definitions bundle `OAIQ083J001` of this split); `OAI.TwoPointCorrelations.OneBounded` and `OAI.TwoPointCorrelations.mrtCofactorPolynomial` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.auxiliary_power_energy_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/RamareProductIntegral.lean (declaration OAI.JointDickman.ramare_product_sparse_integral)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem ramare_product_sparse_integral_jd (B : ℝ) (hB : 1 ≤ B) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ᶠ a : ℝ in atTop, ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (E : Set ℝ) (T τ b K : ℝ), MeasurableSet E → 0 ≤ T → 0 ≤ τ →
      E ⊆ Set.Ioc (-T) T → 2*T ≤ a^B →
      let Qf := mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ))
      (∀ U : Finset ℝ, (∀ t ∈ U, t ∈ E) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
        (U.card:ℝ) ≤ K ∧ ((U.filter (fun t => τ < ‖Qf t‖)).card:ℝ) ≤ a^γ) →
      (∀ t ∈ E, τ < ‖Qf t‖ → ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∫ t in E, ‖Qf t*mrtCofactorPolynomial P F N a t‖^2) ≤
        2*(τ^2*(48000*(2*(1+Real.log (2*T+1))+K*Real.sqrt (2*T)*a/N))+
          b^2*(C/(Real.log a)^2)) := by
  sorry

end JointDickman

end OAI
end
