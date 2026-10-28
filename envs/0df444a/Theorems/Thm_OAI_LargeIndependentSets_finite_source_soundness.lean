-- Prove2me | Theorems.Thm_OAI_LargeIndependentSets_finite_source_soundness
-- name    : OAI.LargeIndependentSets.finite_source_soundness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T01:54:32.715267+00:00
-- url     : https://prove2.me/theorems/bedb8cbc-4603-499f-8790-3aacf84af15b
-- title:
--   OAI.LargeIndependentSets.finite_source_soundness: intermediate lemma from OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LargeIndependentSets.finite_source_soundness` of [lean/OAI/Combinatorics/IndependentSets/Reduction/SamplerParameters.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/Reduction/SamplerParameters.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LargeIndependentSets`, with `open scoped Classical BigOperators`, `open MeasureTheory PhaseTest`):
--
--   ```lean
--   theorem finite_source_soundness {δ : ℝ} (hδ : 0 < δ) :
--       ∃ p : SamplerParameters, ∃ σ : ℚ, 0 < σ ∧ σ < 1 ∧
--       ∀ (U V L R C : Type) [Fintype L] [Fintype R] [Fintype C]
--         [Nonempty L] [Nonempty R] [Nonempty C] (lc : LabelCoverData U V L R C),
--       lc.Sound (σ:ℝ) →
--       (∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
--         ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)) →
--       ∀ A : Finset (p.Vertices L R C), (p.graph lc).IsIndepSet (A : Set _) →
--         (A.card : ℝ) / Fintype.card (p.Vertices L R C) < δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.LargeIndependentSets.GridLocation`, `OAI.LargeIndependentSets.LabelCoverData`, `OAI.LargeIndependentSets.LayerAnswer`, `OAI.LargeIndependentSets.LayerQuestion`, `OAI.LargeIndependentSets.MixedTuple`, `OAI.LargeIndependentSets.SamplerOutcome`, `OAI.LargeIndependentSets.SamplerParameters`, `OAI.LargeIndependentSets.SubchainCoord`, `OAI.LargeIndependentSets.gridAntipode`, `OAI.LargeIndependentSets.mixedTupleFintype`, `OAI.LargeIndependentSets.pathDistance`, `OAI.LargeIndependentSets.BooleanJunta.Cube`, `OAI.LargeIndependentSets.BooleanJunta.cubeFintype`, `OAI.LargeIndependentSets.LabelCoverData.Sound`, `OAI.LargeIndependentSets.ProjectionSystem.linkLength`, `OAI.LargeIndependentSets.RationalLaw.Expanded`, `OAI.LargeIndependentSets.RationalLaw.copies` and `OAI.LargeIndependentSets.SamplerParameters.instNeZeroNatHMulMHPowOfNatK` (definitions bundle `OAIQ069A002` of this split); `OAI.LargeIndependentSets.layeredSystem`, `OAI.LargeIndependentSets.SamplerParameters.Vertices`, `OAI.LargeIndependentSets.SamplerParameters.graph` and `OAI.LargeIndependentSets.SamplerParameters.law` (definitions bundle `OAIQ069A004` of this split).
--
--   **Used by.** The proof of `OAI.LargeIndependentSets.mainTheoremReal` of this split imports it.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/Reduction/SamplerParameters.lean (declaration OAI.LargeIndependentSets.finite_source_soundness)

import Mathlib
import Definitions.Def_OAIQ069A004

section

attribute [-instance] _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators
open MeasureTheory PhaseTest

theorem finite_source_soundness {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : SamplerParameters, ∃ σ : ℚ, 0 < σ ∧ σ < 1 ∧
    ∀ (U V L R C : Type) [Fintype L] [Fintype R] [Fintype C]
      [Nonempty L] [Nonempty R] [Nonempty C] (lc : LabelCoverData U V L R C),
    lc.Sound (σ:ℝ) →
    (∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)) →
    ∀ A : Finset (p.Vertices L R C), (p.graph lc).IsIndepSet (A : Set _) →
      (A.card : ℝ) / Fintype.card (p.Vertices L R C) < δ := by
  sorry

end LargeIndependentSets

end OAI
end
