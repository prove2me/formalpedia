-- Prove2me | Theorems.Thm_OAI_Release061_NashBoundaryScalingChart_independent_support_rows
-- name    : OAI.Release061.NashBoundaryScalingChart.independent_support_rows
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:47:15.84184+00:00
-- url     : https://prove2.me/theorems/cba41d83-f691-4ab9-bc82-83de8164f70a
-- title:
--   OAI.Release061.NashBoundaryScalingChart.independent_support_rows: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.NashBoundaryScalingChart.independent_support_rows` of [lean/OAI/Analysis/SymmetricDomains/IndependentSupportRows.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/IndependentSupportRows.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061.NashBoundaryScalingChart`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology Metric`, `open scoped Classical`):
--
--   ```lean
--   theorem independent_support_rows (s : NashBoundaryScalingChart c x)
--       (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
--       (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
--       (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)))
--       (F : Affine m → Affine N) (G : Affine N → Affine m)
--       (hF0 : F 0=q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
--       (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
--       (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y)
--       (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V)
--       {k : ℕ} (h : Fin k → Affine N → ℂ)
--       (hlog : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0)
--       (hI : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap))
--       (hzero : ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ q) x)=0) :
--       (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (s.forward z))) 0) ∧
--       ∃ β : Fin k → Fin s.normalDim → ℝ, LinearIndependent ℝ β ∧
--         ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
--           Complex.I * ∑ j, (β i j : ℂ)*z.2 j
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.NashBoundaryChart`, `OAI.Release061.NashBoundaryScalingChart`, `OAI.Release061.NashBoundaryChart.GoodAt`, `OAI.Release061.NashBoundaryScalingChart.HasCutoffs` and `OAI.Release061.NashBoundaryScalingChart.forward` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.original_supported_hermitian_model` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/IndependentSupportRows.lean (declaration OAI.Release061.NashBoundaryScalingChart.independent_support_rows)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem independent_support_rows (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)))
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0=q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V)
    {k : ℕ} (h : Fin k → Affine N → ℂ)
    (hlog : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0)
    (hI : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap))
    (hzero : ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ q) x)=0) :
    (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (s.forward z))) 0) ∧
    ∃ β : Fin k → Fin s.normalDim → ℝ, LinearIndependent ℝ β ∧
      ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
        Complex.I * ∑ j, (β i j : ℂ)*z.2 j := by
  sorry
end NashBoundaryScalingChart
end Release061

end

end OAI
end
