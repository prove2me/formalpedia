-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_ReducedTopology_scheduledMarkerDefect_covariance_sat
-- name    : OAI.DilutedSpinGlass.ReducedTopology.scheduledMarkerDefect_covariance_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:06.525301+00:00
-- url     : https://prove2.me/theorems/7ff1549e-7678-4129-a435-2a5adfac4723
-- title:
--   OAI.DilutedSpinGlass.ReducedTopology.scheduledMarkerDefect_covariance_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.ReducedTopology.scheduledMarkerDefect_covariance` of [lean/OAI/Probability/DilutedSpin/MarkerScheduledIdentity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MarkerScheduledIdentity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.ReducedTopology`, with `open _root_.MeasureTheory PrescribedTree`):
--
--   ```lean
--   lemma scheduledMarkerDefect_covariance_sat (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
--       (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
--       (K : (z : Z) → KernelTower (Ω z) L) (m : Fin (L+1) → ℝ)
--       (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last L)=1)
--       (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
--       let A := realize n (d+1) S q
--       let S' := stem (unary A) d
--       let T' := stem (markerFork A) d
--       let a := firstLeaf S'
--       let q' := markerColorTarget A d
--       markerMatrixCovariance μ Ω (heightCast e.symm S') (leafHeightCast e.symm S' a)
--         (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q' c)) K m V =
--         partialKappa T' (fun j => m (Fin.cast (congrArg (fun a => a+1) e.symm) j))
--           (Finset.univ.image q') * scheduledMarkerDefect μ Ω d S q K V
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.ReducedTopology`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.PrescribedTree.firstLeaf`, `OAI.DilutedSpinGlass.PrescribedTree.heightCast`, `OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq`, `OAI.DilutedSpinGlass.PrescribedTree.leafFintype`, `OAI.DilutedSpinGlass.PrescribedTree.leafHeightCast`, `OAI.DilutedSpinGlass.PrescribedTree.markerColorTarget`, `OAI.DilutedSpinGlass.PrescribedTree.markerFork`, `OAI.DilutedSpinGlass.PrescribedTree.markerMatrixCovariance`, `OAI.DilutedSpinGlass.PrescribedTree.partialKappa`, `OAI.DilutedSpinGlass.PrescribedTree.stem`, `OAI.DilutedSpinGlass.PrescribedTree.unary`, `OAI.DilutedSpinGlass.ReducedTopology.Vertex`, `OAI.DilutedSpinGlass.ReducedTopology.realize` and `OAI.DilutedSpinGlass.ReducedTopology.scheduledMarkerDefect` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MarkerScheduledIdentity.lean (declaration OAI.DilutedSpinGlass.ReducedTopology.scheduledMarkerDefect_covariance)

import Mathlib
import Definitions.Def_OAIQ041D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {L N : ℕ}

lemma scheduledMarkerDefect_covariance_sat (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
    (K : (z : Z) → KernelTower (Ω z) L) (m : Fin (L+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last L)=1)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
    let A := realize n (d+1) S q
    let S' := stem (unary A) d
    let T' := stem (markerFork A) d
    let a := firstLeaf S'
    let q' := markerColorTarget A d
    markerMatrixCovariance μ Ω (heightCast e.symm S') (leafHeightCast e.symm S' a)
      (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q' c)) K m V =
      partialKappa T' (fun j => m (Fin.cast (congrArg (fun a => a+1) e.symm) j))
        (Finset.univ.image q') * scheduledMarkerDefect μ Ω d S q K V := by
  sorry

end DilutedSpinGlass.ReducedTopology

end

end OAI
end
