-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_prefix_band
-- name    : OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:53:43.227887+00:00
-- url     : https://prove2.me/theorems/f926ffd8-abc0-4061-b3ad-bd8979a8721a
-- title:
--   OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band` of [lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/PrefixBandAssembly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/PrefixBandAssembly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.PositiveDistanceData`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem uniform_prefix_band {sig kap lam T eps : ℝ}
--       (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
--       (hT : 0 ≤ T) (heps : 0 < eps) {J : ℕ} (hJ : 0 < J)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
--       (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
--       ∃ C : ℝ, 0 < C ∧ ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
--       d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
--       ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
--       0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
--       d.X.length = d.a → d.Y.length = d.a →
--       100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
--       dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
--       let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
--       let p := policyDepth A d.N d.q d.a d.t
--       2*p ≤ d.a+d.t →
--       d.coincidence.toReal ≤ C*(1+2*(d.N:ℝ)) *
--         (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
--         ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps) *
--           d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.height`, `OAI.PlanarFalconer.policyDepth`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare.center`, `OAI.PlanarFalconer.DyadicSquare.descendant`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.coincidence`, `OAI.PlanarFalconer.PositiveDistanceData.prefixLowMaximum` and `OAI.PlanarFalconer.PositiveDistanceData.prefixSuccessorSupremum` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_recursive_energy_rules` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/PrefixBandAssembly.lean (declaration OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
namespace PositiveDistanceData

theorem uniform_prefix_band {sig kap lam T eps : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heps : 0 < eps) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ C : ℝ, 0 < C ∧ ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    d.coincidence.toReal ≤ C*(1+2*(d.N:ℝ)) *
      (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps) *
        d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T)) := by
  sorry

end PositiveDistanceData

end PlanarFalconer

end OAI
end
