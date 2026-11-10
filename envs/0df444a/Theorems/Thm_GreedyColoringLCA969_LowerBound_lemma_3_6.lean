-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_lemma_3_6
-- name    : GreedyColoringLCA969.LowerBound.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:43:19.419861+00:00
-- url     : https://prove2.me/theorems/422ec93a-5ce9-4180-8432-7bc895c792b3
-- title:
--   Lemma 3.6 — directed-neighborhood packing with a shared exceptional set
-- statement:
--   Let $H$ be a directed graph on $N$ vertices, allowing self-loops, and let the integer $D\ge1$ bound every outdegree. Let $V'\subseteq V(H)$ have size $N'\ge2$, and suppose every vertex of $V'$ has a self-loop. If
--
--   $$N'\ge 2D(\log_2N')^D,$$
--
--   there are $U\subseteq V'$ and $S\subseteq V(H)$ such that
--
--   $$|U|\ge\frac{\log_2N'}{2D},\qquad |S|\le D,\qquad U\cap S=\varnothing,$$
--
--   and for every two distinct $u,v\in U$,
--
--   $$N^+(u)\cap N^+(v)\subseteq S.$$
--
--   This gives the exact packing condition used in the amplification argument, with no bound on the ambient number of vertices. A loop contributes one out-neighbor. The superscript $D$ in the hypothesis denotes a power, and every logarithm has base two.
--
--   Differences from the source:
--   - encoding: a finite directed graph, vertex subsets and integer degree bound → a relation on Fin N and finite subsets, with natural D at least one; reason: every finite directed graph, including loops, is represented; natural D covers exactly the source positive integers
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Lemma 3.6, p.12 (PDF 13); proof pp.12–13 (PDF 13–14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Lemma 3.6, printed p.12 / PDF 13. D is a power in the numerical hypothesis,
not the base of the logarithm. Loops are allowed, and required on Vprime. -/
theorem lemma_3_6 (N D : ℕ) (hD : 1 ≤ D) (H : Digraph N)
    (hOut : ∀ u, (outNeighbors H u).card ≤ D) (Vprime : Finset (Fin N))
    (hSize : 2 ≤ Vprime.card) (hLoops : ∀ u ∈ Vprime, H u u)
    (hLarge : (2 : ℝ) * D * (log2 (Vprime.card : ℝ)) ^ D ≤ (Vprime.card : ℝ)) :
    ∃ U S : Finset (Fin N), U ⊆ Vprime ∧
      log2 (Vprime.card : ℝ) / (2 * D) ≤ (U.card : ℝ) ∧ S.card ≤ D ∧
      Disjoint U S ∧
      ∀ u ∈ U, ∀ v ∈ U, u ≠ v → outNeighbors H u ∩ outNeighbors H v ⊆ S := by sorry

end GreedyColoringLCA969.LowerBound
