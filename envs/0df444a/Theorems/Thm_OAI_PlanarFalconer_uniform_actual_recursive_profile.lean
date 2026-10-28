-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_recursive_profile
-- name    : OAI.PlanarFalconer.uniform_actual_recursive_profile
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:57:24.987052+00:00
-- url     : https://prove2.me/theorems/e8f686ed-4272-4281-a03c-185dec900e43
-- title:
--   OAI.PlanarFalconer.uniform_actual_recursive_profile: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_recursive_profile` of [lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ActualRecursiveProfile.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ActualRecursiveProfile.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem uniform_actual_recursive_profile {lam sig kap eta : ℝ}
--       (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
--       (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta) (K₀ : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
--       (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
--       ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
--         e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
--         e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
--         ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
--         ∀ root : BranchState, root.Valid e.N e.sig → root.index = 0 →
--         root.start+10*e.q ≤ root.finish → ∀ x, e.energies K₀ Ψ root x →
--         x ≤ ((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
--           +500*kap+10^6*(lam+sig)/kap+eta)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.BranchState`, `OAI.PlanarFalconer.RecursiveEnvironment`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.potential`, `OAI.PlanarFalconer.sourcePolicyBlock`, `OAI.PlanarFalconer.sourceSmoothingLevels`, `OAI.PlanarFalconer.BranchState.Valid`, `OAI.PlanarFalconer.BranchState.finish`, `OAI.PlanarFalconer.BranchState.index`, `OAI.PlanarFalconer.BranchState.start`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.RecursiveEnvironment.energies` and `OAI.PlanarFalconer.RecursiveEnvironment.profile` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_outer_root_graph_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ActualRecursiveProfile.lean (declaration OAI.PlanarFalconer.uniform_actual_recursive_profile)

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

theorem uniform_actual_recursive_profile {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      ∀ root : BranchState, root.Valid e.N e.sig → root.index = 0 →
      root.start+10*e.q ≤ root.finish → ∀ x, e.energies K₀ Ψ root x →
      x ≤ ((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
        +500*kap+10^6*(lam+sig)/kap+eta) := by
  sorry

end PlanarFalconer

end OAI
end
