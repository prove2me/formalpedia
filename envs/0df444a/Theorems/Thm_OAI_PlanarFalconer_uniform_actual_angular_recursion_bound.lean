-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_angular_recursion_bound
-- name    : OAI.PlanarFalconer.uniform_actual_angular_recursion_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:56:14.109384+00:00
-- url     : https://prove2.me/theorems/a0e79298-0b30-4741-8b41-1f2231019c57
-- title:
--   OAI.PlanarFalconer.uniform_actual_angular_recursion_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_angular_recursion_bound` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualAngularRecursionBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualAngularRecursionBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem uniform_actual_angular_recursion_bound {lam sig kap eps : ℝ}
--       (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
--       (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
--       ∃ N₀ : ℕ, ∀ d : AngularStateData,
--         d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
--         d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N →
--         d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
--         d.branchState.Valid d.N d.sig → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
--         d.X.length = d.a → d.Y.length = d.a →
--         ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
--         ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K) →
--         ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
--         ∀ M : ℝ, 0 ≤ M →
--         (∀ p l, BranchStep d.profile d.N d.q d.sig d.branchState l (.H d.a₀ d.t₀ p d.v d.i) →
--           ∀ row ∈ d.children p,
--           ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState l (.H d.a₀ d.t₀ p d.v d.i)) *
--             ((d.successor p row).energy k h Ψ).toReal ≤ M) →
--         (∀ b, BranchStep d.profile d.N d.q d.sig d.branchState .far (.D b d.v (d.i+1)) →
--           ∀ row ∈ d.children b, ∀ col ∈ d.children b, angularSeparated d.Q d.Q b row col →
--           ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
--             ((d.distanceSuccessor b).atCells row.1 col.1).coincidence.toReal ≤ M ∧
--           ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
--             ((d.distanceSuccessor b).atCells row.2 col.2).coincidence.toReal ≤ M) →
--         d.energy k h Ψ ≠ ⊤ ∧
--           (d.energy k h Ψ).toReal ≤ ((d.N:ℝ)+1)*M+((2:ℝ)^d.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.AngularStateData`, `OAI.PlanarFalconer.BranchLabel`, `OAI.PlanarFalconer.BranchStep`, `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.angularSeparated`, `OAI.PlanarFalconer.branchExponent`, `OAI.PlanarFalconer.sourcePolicyBlock`, `OAI.PlanarFalconer.sourceSmoothingLevels`, `OAI.PlanarFalconer.AngularStateData.branchState`, `OAI.PlanarFalconer.AngularStateData.children`, `OAI.PlanarFalconer.AngularStateData.distanceSuccessor`, `OAI.PlanarFalconer.AngularStateData.energy`, `OAI.PlanarFalconer.AngularStateData.profile`, `OAI.PlanarFalconer.AngularStateData.retainedList`, `OAI.PlanarFalconer.AngularStateData.successor`, `OAI.PlanarFalconer.BranchState`, `OAI.PlanarFalconer.BranchState.Valid`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.atCells` and `OAI.PlanarFalconer.PositiveDistanceData.coincidence` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_recursive_energy_rules` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/ActualAngularRecursionBound.lean (declaration OAI.PlanarFalconer.uniform_actual_angular_recursion_bound)

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

theorem uniform_actual_angular_recursion_bound {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
      d.branchState.Valid d.N d.sig → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ p l, BranchStep d.profile d.N d.q d.sig d.branchState l (.H d.a₀ d.t₀ p d.v d.i) →
        ∀ row ∈ d.children p,
        ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState l (.H d.a₀ d.t₀ p d.v d.i)) *
          ((d.successor p row).energy k h Ψ).toReal ≤ M) →
      (∀ b, BranchStep d.profile d.N d.q d.sig d.branchState .far (.D b d.v (d.i+1)) →
        ∀ row ∈ d.children b, ∀ col ∈ d.children b, angularSeparated d.Q d.Q b row col →
        ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
          ((d.distanceSuccessor b).atCells row.1 col.1).coincidence.toReal ≤ M ∧
        ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
          ((d.distanceSuccessor b).atCells row.2 col.2).coincidence.toReal ≤ M) →
      d.energy k h Ψ ≠ ⊤ ∧
        (d.energy k h Ψ).toReal ≤ ((d.N:ℝ)+1)*M+((2:ℝ)^d.N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end
