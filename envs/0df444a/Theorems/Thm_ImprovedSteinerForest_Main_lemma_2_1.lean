-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_lemma_2_1
-- name    : ImprovedSteinerForest.Main.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:28:32.036537+00:00
-- url     : https://prove2.me/theorems/d1fca4fc-f144-48b9-a06d-b34109c1c1ca
-- title:
--   Lemma 2.1 — extended growth gives a feasible forest of cost ≤ 2(1+ε)ℓ in polynomial time; polynomially many phases; factor two at ε = 0
-- statement:
--   Fix a rational $\varepsilon\ge 0$. There is a deterministic polynomial-time algorithm $M$ on binary strings and a polynomial $q$ such that, for every feasible Steiner Forest instance $I$ with code $\langle I\rangle$:
--
--   - extended moat growth with parameter $\varepsilon$ has a run on $I$;
--   - for its run $R$, $M(\langle I\rangle)$ is the code of an edge set $F$ that is a forest, is feasible, and satisfies
--   $$c(F)\le 2(1+\varepsilon)\,\ell,$$
--   and, when $\varepsilon=0$, also $c(F)\le 2\,\mathrm{opt}$;
--   - the numbers of positive phases and of support cuts of $R$ are at most $q(|\langle I\rangle|)$, and every positive phase duration and every support-cut weight has bit length at most $q(|\langle I\rangle|)$.
--
--   This is the starting point of every call: the growth history is computable in polynomial time and its forest is within $2(1+\varepsilon)$ of the lower bound $\ell\le\mathrm{opt}$; at $\varepsilon=0$ it is the classical factor-two moat growth that the algorithm uses at depth zero.
--
--   **Formalization Note.** One machine and one polynomial per value of $\varepsilon$ ("All algorithm parameters are fixed constants", p. 13), fixed before the instance.
--
--   Differences from the source:
--   - generalization: finite undirected network → multigraph edge list on `Fin n` with loops, parallel edges and repeated labelled pairs; reason: contraction produces multigraphs (p. 13); a simple network is a special case.
--   - generalization: growth on the preprocessed graph of a call (zero-cost components contracted, satisfied demands removed, every cost positive, pp. 13–14) → growth run directly on any instance with nonnegative costs; reason: zero-cost edges are tight at time zero and merge in zero-duration steps; the preprocessed graph is a special case.
--   - encoding: "in deterministic polynomial time" → `∃ M, PolyTimeComputable M` mapping `encInst I` to `encEdgeSet I F`; reason: the bit model of p. 13 (vertex count in unary, rationals in binary).
--   - encoding: "polynomially many positive phases and support cuts … polynomial bit length" → one polynomial `q` in the code length bounding both counts and `ratBitLength` of every duration and weight; reason: the meaning of "polynomially many" and "polynomial bit length" in the input size.
--   - encoding: "the process" → any record `R` with `IsGrowthRun ε I R` (the run is unique), whose existence on every feasible instance is a clause; reason: a continuous-time process recorded by its steps.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 15, Lemma 2.1

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_ImprovedSteinerForest_Main_Instance
import Definitions.Def_ImprovedSteinerForest_Main_Encoding
import Definitions.Def_ImprovedSteinerForest_Main_Growth
open QAlgorithms.Complexity

namespace ImprovedSteinerForest.Main

/-- Lemma 2.1 (p. 15): for each fixed rational `ε ≥ 0`, extended moat growth gives, in
deterministic polynomial time, a feasible forest of cost at most `2(1 + ε)ℓ`; it has polynomially
many positive phases and support cuts, whose durations and weights have polynomial bit length; at
`ε = 0` the factor is at most two. -/
theorem lemma_2_1 (ε : ℚ) (hε : 0 ≤ ε) :
    ∃ M : Str → Str, PolyTimeComputable M ∧ ∃ q : Polynomial ℕ,
      ∀ I : Instance, I.IsFeasibleInst →
        (∃ R : GrowthRun I, IsGrowthRun ε I R) ∧
        ∀ R : GrowthRun I, IsGrowthRun ε I R →
          (∃ F : Finset I.Edge, M (encInst I) = encEdgeSet I F ∧ I.IsForest F ∧ I.Feasible F ∧
            I.cost F ≤ 2 * (1 + ε) * R.ell ∧ (ε = 0 → I.cost F ≤ 2 * I.opt)) ∧
          R.positivePhases.card ≤ q.eval (encInst I).length ∧
          R.supportCuts.card ≤ q.eval (encInst I).length ∧
          (∀ k ∈ R.positivePhases, ratBitLength (R.dur k) ≤ q.eval (encInst I).length) ∧
          (∀ U ∈ R.supportCuts, ratBitLength (R.y U) ≤ q.eval (encInst I).length) := by sorry

end ImprovedSteinerForest.Main
