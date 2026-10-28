-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_recursive_energy_rules
-- name    : OAI.PlanarFalconer.uniform_recursive_energy_rules
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:58:35.102758+00:00
-- url     : https://prove2.me/theorems/0e93f518-a8ac-460f-91bf-edd2e75d6e7c
-- title:
--   OAI.PlanarFalconer.uniform_recursive_energy_rules: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_recursive_energy_rules` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/RecursiveEnergyFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/RecursiveEnergyFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem uniform_recursive_energy_rules {lam sig kap eps tau T : ℝ}
--       (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
--       (hgap : sig < kap/1000) (heps : 0 < eps) (htau : 0 < tau) (hT : 0 < T) (K₀ : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
--       (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
--       ∃ K : ℕ, K₀ ≤ K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
--         e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
--         e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
--         ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
--         (∀ s : BranchState, s.Valid e.N e.sig → s.finish ≤ s.start+100*e.q → ∀ x, e.energies K Ψ s x →
--           x ≤ ((2:ℝ)^e.N)^(200*(e.q:ℝ)/e.N+12*lam+tau)) ∧
--         (∀ s : BranchState, s.Valid e.N e.sig → s.index+1 ≤ e.J → s.start+100*e.q < s.finish →
--           ∀ M : ℝ, 0 ≤ M → ((2:ℝ)^e.N)^(12*lam+eps) ≤ M →
--           (∀ u l, BranchStep e.profile e.N e.q e.sig s l u → ∀ x, e.energies K Ψ u x →
--             ((2:ℝ)^e.N)^(branchExponent e.profile lam sig eps s l u)*x ≤ M) →
--           ∀ x, e.energies K Ψ s x → x ≤ ((e.N:ℝ)+3)*M+((2:ℝ)^e.N)^(-T))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.BranchLabel`, `OAI.PlanarFalconer.BranchState`, `OAI.PlanarFalconer.BranchStep`, `OAI.PlanarFalconer.RecursiveEnvironment`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.branchExponent`, `OAI.PlanarFalconer.sourcePolicyBlock`, `OAI.PlanarFalconer.sourceSmoothingLevels`, `OAI.PlanarFalconer.BranchState.Valid`, `OAI.PlanarFalconer.BranchState.finish`, `OAI.PlanarFalconer.BranchState.index`, `OAI.PlanarFalconer.BranchState.start`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.RecursiveEnvironment.energies` and `OAI.PlanarFalconer.RecursiveEnvironment.profile` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_recursive_profile` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/RecursiveEnergyFamily.lean (declaration OAI.PlanarFalconer.uniform_recursive_energy_rules)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_recursive_energy_rules {lam sig kap eps tau T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (htau : 0 < tau) (hT : 0 < T) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ K : ℕ, K₀ ≤ K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      (∀ s : BranchState, s.Valid e.N e.sig → s.finish ≤ s.start+100*e.q → ∀ x, e.energies K Ψ s x →
        x ≤ ((2:ℝ)^e.N)^(200*(e.q:ℝ)/e.N+12*lam+tau)) ∧
      (∀ s : BranchState, s.Valid e.N e.sig → s.index+1 ≤ e.J → s.start+100*e.q < s.finish →
        ∀ M : ℝ, 0 ≤ M → ((2:ℝ)^e.N)^(12*lam+eps) ≤ M →
        (∀ u l, BranchStep e.profile e.N e.q e.sig s l u → ∀ x, e.energies K Ψ u x →
          ((2:ℝ)^e.N)^(branchExponent e.profile lam sig eps s l u)*x ≤ M) →
        ∀ x, e.energies K Ψ s x → x ≤ ((e.N:ℝ)+3)*M+((2:ℝ)^e.N)^(-T)) := by
  sorry

end PlanarFalconer

end OAI
end
