-- Prove2me | Theorems.Thm_OAI_Falconer_exists_uniform_outer_angular_decay
-- name    : OAI.Falconer.exists_uniform_outer_angular_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:51:14.777411+00:00
-- url     : https://prove2.me/theorems/1f9ee4fa-318f-462e-a09b-d1046ab0e9e3
-- title:
--   OAI.Falconer.exists_uniform_outer_angular_decay: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_uniform_outer_angular_decay` of [lean/OAI/MeasureTheory/Falconer/Angular/OuterAngularDecay.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/OuterAngularDecay.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped SchwartzMap ContDiff`, `open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)`):
--
--   ```lean
--   theorem exists_uniform_outer_angular_decay
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
--       (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
--       (hη : 0 < η) (hη1 : η ≤ 1)
--       (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
--       (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
--       {χ β : ℝ} (hχ : 0 < χ) (hβ : 0 < β)
--       (hκsmall : κ ≤ 1/1000) (hTβ : β/2 ≤ T)
--       (hentrySmall : β+((m+3:ℕ)+4)*lam < χ/4)
--       (hdecay : ((m+3:ℕ)+4)*lam+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ ≤ β/8)
--       (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
--       (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
--       (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
--       (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
--       {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
--       (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
--       ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
--         ∀ P Q : PolicyJetData m, P.N = Q.N → P.lam = lam → Q.lam = lam →
--         P.s = (m+3:ℕ)/2+χ → Q.s = (m+3:ℕ)/2+χ →
--         P.σ = σ → Q.σ = σ → P.J = sourceSmoothingLevels σ κ → Q.J = sourceSmoothingLevels σ κ →
--         P.q = sourcePolicyBlock P.N κ → Q.q = sourcePolicyBlock Q.N κ →
--         P.Z = Z → Q.Z = Z → P.a = 0 → Q.a = 0 → P.t = P.N → Q.t = Q.N →
--         N₀ ≤ P.N → P.i = 0 → Q.i = 0 →
--         P.policy = profileExcess (d := m+3) P.profile P.N →
--         Q.policy = profileExcess (d := m+3) Q.profile Q.N →
--         (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
--           dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
--         (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Q.masks b,
--           dist w c ≤ descriptorMaskRadius Q.N Q.σ b/2) →
--         (∀ b, ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
--           descriptorMaskRadius P.N P.σ b/2 ≤ dist w z) →
--         (∀ b, ∀ w ∈ Q.masks b, ∀ z ∈ Q.masks b, w ≠ z →
--           descriptorMaskRadius Q.N Q.σ b/2 ≤ dist w z) →
--         ∃ c : ℕ, 4*c ≤ P.N ∧ c+100*P.q < P.N ∧
--           β*P.N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
--         ∀ (f : DescriptorJetSymbol (m+1) K L (P.outerList c) 1)
--           (g : DescriptorJetSymbol (m+1) K L (Q.outerList c) 1),
--         independentAngularEnergy P.a P.t Ψ
--           (fun z => endpointTransform (P.ρ.restrict (P.Q.descendant P.X).carrier)
--             (profileModelMass P.profile P.N P.a)
--             (f.value P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z) z.1 z.2)
--           (fun z => endpointTransform (Q.ρ.restrict (Q.Q.descendant Q.X).carrier)
--             (profileModelMass Q.profile Q.N Q.a)
--             (g.value Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Q.Z) z.1 z.2) ≤
--         ((2:ℝ)^P.N)^(-β/4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.sourcePolicyBlock` and `OAI.PlanarFalconer.sourceSmoothingLevels` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.DescriptorJetSymbol`, `OAI.Falconer.PolicyJetData`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorMaskRadius`, `OAI.Falconer.dimensionalBranchReserve`, `OAI.Falconer.endpointTransform`, `OAI.Falconer.independentAngularEnergy`, `OAI.Falconer.profileExcess`, `OAI.Falconer.profileModelMass`, `OAI.Falconer.DescriptorJetSymbol.value`, `OAI.Falconer.DyadicCube.carrier`, `OAI.Falconer.DyadicCube.descendant` and `OAI.Falconer.PolicyJetData.outerList` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.outerGraphLoss` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.PublishedGnomonicSurface`, `OAI.Falconer.PublishedQuadraticStationary` and `OAI.Falconer.outerRootLoss` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.exists_regular_class_shell` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/OuterAngularDecay.lean (declaration OAI.Falconer.exists_uniform_outer_angular_decay)

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
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

theorem exists_uniform_outer_angular_decay
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    {χ β : ℝ} (hχ : 0 < χ) (hβ : 0 < β)
    (hκsmall : κ ≤ 1/1000) (hTβ : β/2 ≤ T)
    (hentrySmall : β+((m+3:ℕ)+4)*lam < χ/4)
    (hdecay : ((m+3:ℕ)+4)*lam+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ ≤ β/8)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ P Q : PolicyJetData m, P.N = Q.N → P.lam = lam → Q.lam = lam →
      P.s = (m+3:ℕ)/2+χ → Q.s = (m+3:ℕ)/2+χ →
      P.σ = σ → Q.σ = σ → P.J = sourceSmoothingLevels σ κ → Q.J = sourceSmoothingLevels σ κ →
      P.q = sourcePolicyBlock P.N κ → Q.q = sourcePolicyBlock Q.N κ →
      P.Z = Z → Q.Z = Z → P.a = 0 → Q.a = 0 → P.t = P.N → Q.t = Q.N →
      N₀ ≤ P.N → P.i = 0 → Q.i = 0 →
      P.policy = profileExcess (d := m+3) P.profile P.N →
      Q.policy = profileExcess (d := m+3) Q.profile Q.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Q.masks b,
        dist w c ≤ descriptorMaskRadius Q.N Q.σ b/2) →
      (∀ b, ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
        descriptorMaskRadius P.N P.σ b/2 ≤ dist w z) →
      (∀ b, ∀ w ∈ Q.masks b, ∀ z ∈ Q.masks b, w ≠ z →
        descriptorMaskRadius Q.N Q.σ b/2 ≤ dist w z) →
      ∃ c : ℕ, 4*c ≤ P.N ∧ c+100*P.q < P.N ∧
        β*P.N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      ∀ (f : DescriptorJetSymbol (m+1) K L (P.outerList c) 1)
        (g : DescriptorJetSymbol (m+1) K L (Q.outerList c) 1),
      independentAngularEnergy P.a P.t Ψ
        (fun z => endpointTransform (P.ρ.restrict (P.Q.descendant P.X).carrier)
          (profileModelMass P.profile P.N P.a)
          (f.value P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z) z.1 z.2)
        (fun z => endpointTransform (Q.ρ.restrict (Q.Q.descendant Q.X).carrier)
          (profileModelMass Q.profile Q.N Q.a)
          (g.value Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Q.Z) z.1 z.2) ≤
      ((2:ℝ)^P.N)^(-β/4) := by
  sorry

end Falconer

end OAI
end
