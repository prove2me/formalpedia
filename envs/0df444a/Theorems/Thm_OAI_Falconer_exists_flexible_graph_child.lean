-- Prove2me | Theorems.Thm_OAI_Falconer_exists_flexible_graph_child
-- name    : OAI.Falconer.exists_flexible_graph_child
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:49:36.725212+00:00
-- url     : https://prove2.me/theorems/8fc4220d-b3cb-43eb-872f-43a089373f9d
-- title:
--   OAI.Falconer.exists_flexible_graph_child: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_flexible_graph_child` of [lean/OAI/MeasureTheory/Falconer/Graphs/FlexibleGraphChild.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Graphs/FlexibleGraphChild.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped SchwartzMap ContDiff`, `open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)`):
--
--   ```lean
--   theorem exists_flexible_graph_child
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
--       (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
--       (hη : 0 < η) (hη1 : η ≤ 1)
--       (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
--       (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
--       (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
--       (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
--       (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
--       (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
--       {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
--       (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
--       ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
--         ∀ k l : ℕ, k ≤ K → L ≤ l →
--         ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ →
--         P.J = sourceSmoothingLevels σ κ → P.q = sourcePolicyBlock P.N κ →
--         N₀ ≤ P.N → P.i = 0 → P.policy = profileExcess (d := m+3) P.profile P.N →
--         (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
--           dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
--         (P.t₀:ℝ) ≤ P.t+P.σ*P.N →
--         ∀ c : ℕ, P.a ≤ c → c+100*P.q < P.t →
--         P.graphChild k l c Ψ ≤ (Z/P.Z)^4*P.rootBoundAt c σ κ η
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.sourcePolicyBlock` and `OAI.PlanarFalconer.sourceSmoothingLevels` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.PolicyJetData`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorMaskRadius`, `OAI.Falconer.dimensionalBranchReserve`, `OAI.Falconer.profileExcess`, `OAI.Falconer.PolicyJetData.graphChild` and `OAI.Falconer.PolicyJetData.rootBoundAt` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface` and `OAI.Falconer.PublishedQuadraticStationary` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.exists_uniform_outer_angular_decay` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Graphs/FlexibleGraphChild.lean (declaration OAI.Falconer.exists_flexible_graph_child)

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

theorem exists_flexible_graph_child
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ k l : ℕ, k ≤ K → L ≤ l →
      ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ →
      P.J = sourceSmoothingLevels σ κ → P.q = sourcePolicyBlock P.N κ →
      N₀ ≤ P.N → P.i = 0 → P.policy = profileExcess (d := m+3) P.profile P.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (P.t₀:ℝ) ≤ P.t+P.σ*P.N →
      ∀ c : ℕ, P.a ≤ c → c+100*P.q < P.t →
      P.graphChild k l c Ψ ≤ (Z/P.Z)^4*P.rootBoundAt c σ κ η := by
  sorry

end Falconer

end OAI
end
