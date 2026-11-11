-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_lemma_2_2
-- name    : ImprovedSteinerForest.Main.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:28:30.956683+00:00
-- url     : https://prove2.me/theorems/40777d22-3e47-441e-9cce-75605b69a7d3
-- title:
--   Lemma 2.2 — completion [GT26]: a feasible solution of G/𝒮 of cost ≤ 2Σ_U y_U − gain(𝒮) in polynomial time
-- statement:
--   Fix a rational $\varepsilon>0$. There is a deterministic polynomial-time algorithm $M$ such that, for every feasible Steiner Forest instance $I$, its extended growth run $R$ with parameter $\varepsilon$, and every actively connected collection $\mathcal S$ (given as a list $L$ of vertex sets), $M$ maps the code of $I$ followed by the code of $L$ to the code of an edge set $F$ that is a feasible solution of $G/\mathcal S$ and satisfies
--   $$c(F)\le 2\sum_U y_U-\mathrm{gain}(\mathcal S).$$
--
--   This is the completion tool of Gupta and Traub (Lemma 3.6 of arXiv:2511.18460v1): after connecting the sets of $\mathcal S$ in advance, the rest of a solution costs at most the basic bound minus the gain. It is the bridge from auxiliary connections to input forests (Lemma 4.2) and hence to the rounding guarantee.
--
--   **Formalization Note.** One machine per value of $\varepsilon$. A solution of $G/\mathcal S$ is an edge set of $G$ that connects every demand once the vertices of each set of $\mathcal S$ are identified.
--
--   Differences from the source:
--   - generalization: finite undirected network → multigraph edge list on `Fin n` with loops, parallel edges and repeated labelled pairs; reason: contraction produces multigraphs (p. 13); a simple network is a special case.
--   - generalization: growth on the preprocessed graph of a call (zero-cost components contracted, satisfied demands removed, every cost positive, pp. 13–14) → growth run directly on any instance with nonnegative costs; reason: zero-cost edges are tight at time zero and merge in zero-duration steps; the preprocessed graph is a special case.
--   - reading: "Given a growth history … a deterministic polynomial-time algorithm on G/𝒮" → the machine receives the instance code and the code of the collection, not a code of the history; reason: the history is a function of the instance (the run is unique) and is computable in polynomial time (Lemma 2.1), so supplying it adds no information.
--   - encoding: "actively connected collection 𝒮" → a list `L` of vertex sets with `𝒮 = L.toFinset`, coded by `encVertexSets`; reason: an input must be a string.
--   - encoding: "feasible solution on G/𝒮" → `FeasibleMod 𝒮 F` for an edge set `F` of `G`; reason: edges of `G/𝒮` keep their identity and cost (p. 13); loops of `G/𝒮` in `F` only add cost.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 15, Lemma 2.2

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_ImprovedSteinerForest_Main_Instance
import Definitions.Def_ImprovedSteinerForest_Main_Encoding
import Definitions.Def_ImprovedSteinerForest_Main_Growth
open QAlgorithms.Complexity

namespace ImprovedSteinerForest.Main

/-- Lemma 2.2 (Completion [GT26], p. 15): for each fixed rational `ε > 0`, a deterministic
polynomial-time algorithm, given the instance and an actively connected collection `𝒮` of its
growth history, returns a feasible solution of `G/𝒮` of cost at most `2 Σ_U y_U − gain(𝒮)`. -/
theorem lemma_2_2 (ε : ℚ) (hε : 0 < ε) :
    ∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ I : Instance, I.IsFeasibleInst → ∀ R : GrowthRun I, IsGrowthRun ε I R →
        ∀ L : List (Finset (Fin I.n)), R.IsActConnColl L.toFinset →
          ∃ F : Finset I.Edge, M (encInst I ++ encVertexSets I L) = encEdgeSet I F ∧
            I.FeasibleMod L.toFinset F ∧ I.cost F ≤ 2 * R.sumY - R.gain L.toFinset := by sorry

end ImprovedSteinerForest.Main
