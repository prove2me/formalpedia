-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_two_root_has_shell_approximations
-- name    : OAI.PlanarFalconer.two_root_has_shell_approximations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:01:08.80809+00:00
-- url     : https://prove2.me/theorems/9317e115-2d2e-4d3f-9905-5ef16d8118aa
-- title:
--   OAI.PlanarFalconer.two_root_has_shell_approximations: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.two_root_has_shell_approximations` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/TwoRootApproximations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/TwoRootApproximations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set Metric MeasureTheory`, `open scoped ContDiff ENNReal`):
--
--   ```lean
--   theorem two_root_has_shell_approximations (Q : Fin 2 → DyadicSquare)
--       (hQ : ∀ l, (Q l).side = 1)
--       (hlo : 100 ≤ dist (Q 0).center (Q 1).center) (hhi : dist (Q 0).center (Q 1).center ≤ 2000)
--       (μ ν : ProbabilityMeasure Plane) (hμQ : (μ:Measure Plane) (Q 0).carrierᶜ = 0)
--       (hνQ : (ν:Measure Plane) (Q 1).carrierᶜ = 0)
--       {δ β lam sig kap C₀ C₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
--       (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
--       (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
--       (hratio : 10000000*(lam+sig)/kap < β/100)
--       (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
--       (hball₀ : ∀ x : Plane, ∀ r > 0, (μ:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₀*r^(1+δ)))
--       (hball₁ : ∀ x : Plane, ∀ r > 0, (ν:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₁*r^(1+δ)))
--       {p q : ℝ} (hpq : p.HolderConjugate q) {K : ENNReal} (hK : K ≠ ⊤)
--       (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
--       (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
--       (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
--       ∃ hτ : IsFiniteMeasure (weightedDistance ((μ:Measure Plane).prod ν)),
--         HasShellApproximations ⟨weightedDistance ((μ:Measure Plane).prod ν),hτ⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.HasShellApproximations`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.sourceRadialUnit`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.DyadicSquare.center` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.weightedDistance` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.sourceDensityNorm` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.mainTarget_proved` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/TwoRootApproximations.lean (declaration OAI.PlanarFalconer.two_root_has_shell_approximations)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff ENNReal

theorem two_root_has_shell_approximations (Q : Fin 2 → DyadicSquare)
    (hQ : ∀ l, (Q l).side = 1)
    (hlo : 100 ≤ dist (Q 0).center (Q 1).center) (hhi : dist (Q 0).center (Q 1).center ≤ 2000)
    (μ ν : ProbabilityMeasure Plane) (hμQ : (μ:Measure Plane) (Q 0).carrierᶜ = 0)
    (hνQ : (ν:Measure Plane) (Q 1).carrierᶜ = 0)
    {δ β lam sig kap C₀ C₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hball₀ : ∀ x : Plane, ∀ r > 0, (μ:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₀*r^(1+δ)))
    (hball₁ : ∀ x : Plane, ∀ r > 0, (ν:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₁*r^(1+δ)))
    {p q : ℝ} (hpq : p.HolderConjugate q) {K : ENNReal} (hK : K ≠ ⊤)
    (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ hτ : IsFiniteMeasure (weightedDistance ((μ:Measure Plane).prod ν)),
      HasShellApproximations ⟨weightedDistance ((μ:Measure Plane).prod ν),hτ⟩ := by
  sorry

end PlanarFalconer

end OAI
end
