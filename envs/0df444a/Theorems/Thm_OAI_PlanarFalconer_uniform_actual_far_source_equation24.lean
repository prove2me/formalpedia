-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_far_source_equation24
-- name    : OAI.PlanarFalconer.uniform_actual_far_source_equation24
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:57:05.951135+00:00
-- url     : https://prove2.me/theorems/6b7659a8-0d4f-415e-bd7f-814ce413e213
-- title:
--   OAI.PlanarFalconer.uniform_actual_far_source_equation24: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_far_source_equation24` of [lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/ActualFarSourceEquation24.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/ActualFarSourceEquation24.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ENNReal ContDiff`):
--
--   ```lean
--   theorem uniform_actual_far_source_equation24 {Ψ : ℝ → ℝ}
--       (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
--       (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
--       {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
--       {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) (hlam : 0 ≤ lam) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
--       ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
--       (∀ l, ρ l (Q l).carrierᶜ = 0) →
--       ∀ (m : ℝ → ℝ) (q a₀ t₀ a v : ℕ),
--       0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
--       ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
--       (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
--       (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
--       ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
--       a < v-2*sourceFarBuffer N L sig →
--       ∀ (B₀ : ℕ) (δ : ℝ),
--       (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
--       ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
--       (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
--       ∀ A B : CellPath, A.length = a → B.length = a →
--       let d := v-2*sourceFarBuffer N L sig-a
--       let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
--       let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
--       let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
--         ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
--       ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
--         (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
--         (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)‖ ≤
--       ∑ b ∈ Finset.Icc (a+9) (a+d+5),
--         ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+4000*(lam+sig)) *
--           ((D b 0).separatedMaximum (D b 1)
--             (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal +
--         ((2:ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularCellContribution`, `OAI.PlanarFalconer.angularNear`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.remainingPolicyDescriptors`, `OAI.PlanarFalconer.sourceFarBuffer`, `OAI.PlanarFalconer.sourceProductVertices`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.PositiveDistanceData.separatedMaximum` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_angular_recursion_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/ActualFarSourceEquation24.lean (declaration OAI.PlanarFalconer.uniform_actual_far_source_equation24)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_source_equation24 {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) (hlam : 0 ≤ lam) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    a < v-2*sourceFarBuffer N L sig →
    ∀ (B₀ : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let d := v-2*sourceFarBuffer N L sig-a
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
      (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)‖ ≤
    ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+4000*(lam+sig)) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal +
      ((2:ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end
