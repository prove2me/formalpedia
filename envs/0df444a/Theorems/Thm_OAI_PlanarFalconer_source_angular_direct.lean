-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_source_angular_direct
-- name    : OAI.PlanarFalconer.source_angular_direct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:55:05.714983+00:00
-- url     : https://prove2.me/theorems/9a0f4c96-5aca-4fb4-a504-77add27fb5b5
-- title:
--   OAI.PlanarFalconer.source_angular_direct: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.source_angular_direct` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/SourceAngularDirect.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/SourceAngularDirect.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem source_angular_direct {lam sig kap eps : ℝ}
--       (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
--       (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
--       ∃ N₀ : ℕ, ∀ d : AngularStateData,
--         d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
--         d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
--         d.a₀ ≤ d.a → d.a ≤ d.v → d.v ≤ d.t₀ → d.t₀ ≤ d.N →
--         (d.t₀:ℝ) ≤ (d.v:ℝ)+sig*d.N → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
--         d.X.length = d.a → d.Y.length = d.a →
--         ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
--         ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
--         ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
--         d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig ≤ d.a →
--         ∃ e : PolicyDescriptor,
--           DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e ∧
--           let p := descriptorAnchor e
--           d.energy k h Ψ ≠ ⊤ ∧ (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
--           (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
--           (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
--             (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(lam+sig)+eps) *
--               d.childMaximum k h p Ψ + ((2:ℝ)^d.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.AngularStateData`, `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DirectPolicyWitness`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.descriptorAnchor`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.height`, `OAI.PlanarFalconer.sourceFarBuffer`, `OAI.PlanarFalconer.sourcePolicyBlock`, `OAI.PlanarFalconer.sourceSmoothingLevels`, `OAI.PlanarFalconer.AngularStateData.childEnergy`, `OAI.PlanarFalconer.AngularStateData.childMaximum`, `OAI.PlanarFalconer.AngularStateData.energy`, `OAI.PlanarFalconer.AngularStateData.profile`, `OAI.PlanarFalconer.AngularStateData.retainedList` and `OAI.PlanarFalconer.DyadicSquare` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_angular_recursion_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/SourceAngularDirect.lean (declaration OAI.PlanarFalconer.source_angular_direct)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem source_angular_direct {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
      d.a₀ ≤ d.a → d.a ≤ d.v → d.v ≤ d.t₀ → d.t₀ ≤ d.N →
      (d.t₀:ℝ) ≤ (d.v:ℝ)+sig*d.N → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig ≤ d.a →
      ∃ e : PolicyDescriptor,
        DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e ∧
        let p := descriptorAnchor e
        d.energy k h Ψ ≠ ⊤ ∧ (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
        (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
        (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
          (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(lam+sig)+eps) *
            d.childMaximum k h p Ψ + ((2:ℝ)^d.N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end
