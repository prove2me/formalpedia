-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricProfiles_AssignedGeometry_capturePackage
-- name    : OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:30.105485+00:00
-- url     : https://prove2.me/theorems/202f0ddb-f793-434a-bf37-e0730b289fd3
-- title:
--   OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage` of [lean/OAI/Combinatorics/ThinTrees/Metric/ScaleCharging.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Metric/ScaleCharging.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry`, with `open Finset StrongThinTree StrongThinTree.MultiGraph`, `open AlgorithmicThinTrees.MetricProfiles.CompactGeometry`, `open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell`, `open scoped Classical`):
--
--   ```lean
--   lemma capturePackage (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
--       (Y : Fin n → EuclideanSpace ℝ (Fin m))
--       (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
--       (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
--       {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
--       (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
--       (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
--       (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
--       (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
--       (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
--       (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ normDistance (X (G.left e)) (X (G.right e)))
--       (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
--       (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
--         (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
--         (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
--       (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
--         (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
--       (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
--       {q : ℕ} {ρ : ℝ}
--       (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
--       (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card) :
--       let s := α*γ/32
--       let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
--         ((parentBoundary H G t).card : ℝ)
--       ∃B : CapturedFamily H G X (6144/q), B.owners ⊆ T ∧ B.Ratio ρ ∧
--         s*c₁ ≤ B.radius ∧ B.upper ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.MetricProfiles.Doubled`, `OAI.StrongThinTree.MultiGraph.Hierarchy`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.parentBoundary`, `OAI.AlgorithmicThinTrees.MetricProfiles.CompactGeometry.normDistance`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.Ratio`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.mass`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.owners`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.radius` and `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.CapturedFamily.upper` (definitions bundle `OAIQ241TT002` of this split); `OAI.StrongThinTree.MultiGraph` and `OAI.StrongThinTree.MultiGraph.cut` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Metric/ScaleCharging.lean (declaration OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT002

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma capturePackage (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ normDistance (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
    {q : ℕ} {ρ : ℝ}
    (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    ∃B : CapturedFamily H G X (6144/q), B.owners ⊆ T ∧ B.Ratio ρ ∧
      s*c₁ ≤ B.radius ∧ B.upper ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass := by
  sorry

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
end
