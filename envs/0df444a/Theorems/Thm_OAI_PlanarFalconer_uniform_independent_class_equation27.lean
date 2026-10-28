-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_independent_class_equation27
-- name    : OAI.PlanarFalconer.uniform_independent_class_equation27
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:58:14.949185+00:00
-- url     : https://prove2.me/theorems/6323cb87-acb3-4f0a-afa0-807da871c2cb
-- title:
--   OAI.PlanarFalconer.uniform_independent_class_equation27: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_independent_class_equation27` of [lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/IndependentClassEquation27.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/IndependentClassEquation27.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff ENNReal`):
--
--   ```lean
--   theorem uniform_independent_class_equation27 {δ β lam sig kap : ℝ}
--       (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
--       (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
--       (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
--       (hratio : 10000000*(lam+sig)/kap < β/100)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
--       (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
--       ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
--         ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
--         (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
--         100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
--         ∀ B : Fin 2 → ℕ, (∀ l, 0 < B l) →
--         (∀ l, RegularizedProfileData (Q l) (ρ l) N (B l) δ lam (mass l)) →
--         let c := outerEntry (mass 0) (mass 1) N β
--         let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
--           N lam lam sig kap c (Q 0) (Q 1)
--         (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
--           ((2:ℝ)^N)^(-β/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.RootShellData`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare.center`, `OAI.PlanarFalconer.RootShellData.measure` and `OAI.PlanarFalconer.RootShellData.ofOuter` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.outerEntry` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.two_root_has_shell_approximations` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/IndependentClassEquation27.lean (declaration OAI.PlanarFalconer.uniform_independent_class_equation27)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000
import Definitions.Def_OAIQ038F001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem uniform_independent_class_equation27 {δ β lam sig kap : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
      (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ B : Fin 2 → ℕ, (∀ l, 0 < B l) →
      (∀ l, RegularizedProfileData (Q l) (ρ l) N (B l) δ lam (mass l)) →
      let c := outerEntry (mass 0) (mass 1) N β
      let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
        N lam lam sig kap c (Q 0) (Q 1)
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
        ((2:ℝ)^N)^(-β/2) := by
  sorry

end PlanarFalconer

end OAI
end
