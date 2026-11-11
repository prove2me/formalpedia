-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_theorem_1_1
-- name    : ImprovedSteinerForest.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:28:23.67973+00:00
-- url     : https://prove2.me/theorems/861b2eb8-2fb1-4d70-a1ec-49afbb2498f4
-- title:
--   Theorem 1.1 — a deterministic polynomial-time r*-approximation for Steiner Forest, r* = 4857374427850411096559/2500000000000000000000 < 1.94295
-- statement:
--   Let $r^*=\dfrac{4857374427850411096559}{2500000000000000000000}=1.9429497711401644386236<1.94295$. There is one deterministic polynomial-time algorithm $M$ on binary strings such that, for every feasible Steiner Forest instance $I$ (a finite network with nonnegative rational edge costs and a list of demand pairs), $M$ maps the code of $I$ to the code of an edge set $F$ that is a forest, connects both endpoints of every demand pair, and satisfies
--   $$c(F)\le r^*\,\mathrm{opt},$$
--   where $\mathrm{opt}$ is the minimum cost of an edge set connecting every demand pair.
--
--   Agrawal, Klein and Ravi gave factor $2$ in 1991; factor two remained the best known constant for 34 years, until $2-10^{-11}$ (Ahmadi, Gholami, Hajiaghayi, Jabbarzade, Mahdavi, FOCS 2025) and $1.994$ (Gupta and Traub, STOC 2026). The theorem improves the factor to $r^*<1.94295$.
--
--   **Formalization Note.** The machine and its polynomial are fixed before the instance; the running time is polynomial in the length of the input code (vertex count in unary, rational costs in binary). Nothing is required of the output on infeasible inputs.
--
--   Differences from the source:
--   - generalization: finite undirected network → multigraph edge list on `Fin n` with loops, parallel edges and repeated labelled pairs, zero costs allowed; reason: contraction produces multigraphs (p. 13); a simple network with nonnegative rational costs is a special case.
--   - encoding: "a deterministic polynomial-time algorithm" → `∃ M : Str → Str, PolyTimeComputable M` on `encInst I`, output `encEdgeSet I F`; reason: the bit model of p. 13.
--   - reading: "returns a forest of cost at most r* opt" → `IsForest F ∧ Feasible F ∧ c(F) ≤ r*·opt`; reason: the algorithm's output is a feasible forest (p. 18, "Output: A feasible forest") and an approximation algorithm returns a solution.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 5, Theorem 1.1

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_ImprovedSteinerForest_Main_Instance
import Definitions.Def_ImprovedSteinerForest_Main_Encoding
open QAlgorithms.Complexity

namespace ImprovedSteinerForest.Main

/-- Theorem 1.1 (p. 5): one deterministic polynomial-time function on binary strings maps the code
of every feasible Steiner Forest instance to the code of a forest that connects every demand pair
and costs at most `r* · opt`, `r* = 4857374427850411096559/2500000000000000000000`. -/
theorem theorem_1_1 :
    ∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ I : Instance, I.IsFeasibleInst →
        ∃ F : Finset I.Edge, M (encInst I) = encEdgeSet I F ∧ I.IsForest F ∧ I.Feasible F ∧
          I.cost F ≤ (4857374427850411096559 / 2500000000000000000000 : ℚ) * I.opt := by sorry

end ImprovedSteinerForest.Main
