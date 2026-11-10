-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_observation_3_5
-- name    : GreedyColoringLCA969.LowerBound.observation_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:43:23.546581+00:00
-- url     : https://prove2.me/theorems/04b7b9ec-b26d-43cb-9019-fdeda72d1f4d
-- title:
--   Observation 3.5 — a high greedy color forces an exponential-size tree
-- statement:
--   Let $T$ be a finite tree with a greedy coloring $c$ of all of its vertices. For every vertex $v$, writing $\ell=c(v)\in\mathbb Z_{>0}$, one has
--
--   $$|V(T)|\ge2^{\ell-1}.$$
--
--   The coloring is globally proper and every smaller positive color occurs in the neighborhood of each vertex. The observation applies to any greedy ordering, without fixing an ordering or introducing rooted-subtree hypotheses. It supplies the tree-size obstruction needed in the full lower bound.
--
--   **Formalization Note** The vertex $v$ witnesses nonemptiness. Since its color has positive-integer type, natural subtraction of one in the exponent agrees with ordinary integer subtraction.
--
--   Differences from the source:
--   - encoding: vertex identifiers [n] and positive integer colors → Fin n with zero-based identifiers and positive-integer color type; reason: adding one is a bijection on vertex identifiers; colors remain exactly positive integers
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Observation 3.5, p.11 (PDF 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Observation 3.5, printed p.11 / PDF 12. Positivity of l is enforced by its type. -/
theorem observation_3_5 (n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    (c : Fin n → ℕ+) (hc : IsGreedy T c) (v : Fin n) :
    2 ^ ((c v).val - 1) ≤ n := by sorry

end GreedyColoringLCA969.LowerBound
