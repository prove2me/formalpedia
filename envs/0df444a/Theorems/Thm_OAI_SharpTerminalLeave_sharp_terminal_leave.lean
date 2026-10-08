-- Prove2me | Theorems.Thm_OAI_SharpTerminalLeave_sharp_terminal_leave
-- name    : OAI.SharpTerminalLeave.sharp_terminal_leave
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:20.862981+00:00
-- url     : https://prove2.me/theorems/7eb9feee-789a-4d61-adc3-a7c45ea08c2a
-- statement:
--   The theorem states that, for the random triangle-removal process, three limits hold as n tends to infinity. The process starts from the complete graph on n vertices, with graphs represented as sets of 2-element subsets of Fin n. At each step, if the current graph G contains triangles (3-subsets all of whose pairs are edges of G), one triangle is chosen uniformly at random and its three edges are deleted; if there is no triangle, the graph stays unchanged. Running this for C(n,2) steps gives the terminal law on graphs, and expectation and probability are taken with respect to it. Writing normalizedLeave(G) = |E(G)| / n^(3/2) and sharpConstant c = 1/(2√2), the theorem asserts: first, the expected value of (normalizedLeave(G) − c)² tends to 0; second, for every ε > 0, the probability that |normalizedLeave(G) − c| > ε tends to 0; and third, the expected number of edges of the terminal graph divided by n^(3/2) tends to c.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangleRemoval.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangleRemoval.lean; bytes 1423..1847
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TriangleRemoval

namespace OAI

open Filter

open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem sharp_terminal_leave :
    Tendsto (fun n => expectation n (fun G =>
      (normalizedLeave n G - sharpConstant) ^ 2)) atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => probability n (fun G =>
        ε < |normalizedLeave n G - sharpConstant|)) atTop (𝓝 0)) ∧
    Tendsto (fun n => expectation n (fun G => (G.card : ℝ)) / normalization n)
      atTop (𝓝 sharpConstant) := by
  sorry

end SharpTerminalLeave
end OAI
