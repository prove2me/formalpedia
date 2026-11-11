-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_half_bounds
-- name    : OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:28.244363+00:00
-- url     : https://prove2.me/theorems/d9257c7a-0f8f-4709-a343-9b3ab1fd1ce0
-- title:
--   OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds` of [lean/OAI/Combinatorics/ThinTrees/Sparsification/GraphicHalf.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/GraphicHalf.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.GraphicHalf`, with `open Matrix Finset StrongThinTree StrongThinTree.MultiGraph`, `open MetricTests MetricTests.RationalStep Normalization RationalSigning`, `open scoped MatrixOrder`):
--
--   ```lean
--   theorem half_bounds (G : MultiGraph (d+1) m) (B : Finset (Fin m))
--       (X : Matrix (Fin (d+1)) (Fin (d+1)) ℚ) (s : Fin m → ℚ)
--       (hconn : G.Connected univ) (hX : X.map (fun q : ℚ => (q:ℝ)) ∈ metricDomain G)
--       (hQ : ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))).PosDef)
--       {δ : ℝ} (hδ : 0 ≤ δ)
--       (hnorm : ∀e, realVec (fullColumns G B) e ⬝ᵥ
--           (((positiveForm X).map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e)+
--         leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ δ) :
--       let A := halfEdges G B X s
--       let ε := 20*Real.sqrt (2*δ)
--       G.laplacian A ≤ (1/2:ℝ) • G.laplacian B+ε • regularize (X.map (fun q : ℚ => (q:ℝ))) ∧
--       (1/2-ε) • (scaledForm G B s).map (fun q : ℚ => (q:ℝ)) ≤
--         StackedSigning.gram (realVec (scaledColumns G B s)) A
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.GraphicHalf.positiveForm` and `OAI.StrongThinTree.MultiGraph.laplacian` (definitions bundle `OAIQ241TT001` of this split); `OAI.AlgorithmicThinTrees.Normalization.realColumns`, `OAI.AlgorithmicThinTrees.Normalization.realWeights`, `OAI.AlgorithmicThinTrees.RationalSigning.realVec` and `OAI.AlgorithmicThinTrees.StackedSigning.gram` (definitions bundle `OAIQ241TT002` of this split); `OAI.AlgorithmicThinTrees.GraphicHalf.fullColumns`, `OAI.AlgorithmicThinTrees.GraphicHalf.scaledColumns`, `OAI.AlgorithmicThinTrees.GraphicHalf.scaledForm` and `OAI.AlgorithmicThinTrees.Normalization.graphColumns` (definitions bundle `OAIQ241TT005` of this split); `OAI.AlgorithmicThinTrees.MetricTests.metricDomain`, `OAI.AlgorithmicThinTrees.MetricTests.regularize` and `OAI.AlgorithmicThinTrees.Normalization.leverage` (definitions bundle `OAIQ241TT006` of this split); `OAI.AlgorithmicThinTrees.GraphicHalf.halfEdges` (definitions bundle `OAIQ241TT009` of this split); `OAI.StrongThinTree.MultiGraph` and `OAI.StrongThinTree.MultiGraph.Connected` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/GraphicHalf.lean (declaration OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {n d m : ℕ}

theorem half_bounds (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (X : Matrix (Fin (d+1)) (Fin (d+1)) ℚ) (s : Fin m → ℚ)
    (hconn : G.Connected univ) (hX : X.map (fun q : ℚ => (q:ℝ)) ∈ metricDomain G)
    (hQ : ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))).PosDef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnorm : ∀e, realVec (fullColumns G B) e ⬝ᵥ
        (((positiveForm X).map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e)+
      leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ δ) :
    let A := halfEdges G B X s
    let ε := 20*Real.sqrt (2*δ)
    G.laplacian A ≤ (1/2:ℝ) • G.laplacian B+ε • regularize (X.map (fun q : ℚ => (q:ℝ))) ∧
    (1/2-ε) • (scaledForm G B s).map (fun q : ℚ => (q:ℝ)) ≤
      StackedSigning.gram (realVec (scaledColumns G B s)) A := by
  sorry

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end
