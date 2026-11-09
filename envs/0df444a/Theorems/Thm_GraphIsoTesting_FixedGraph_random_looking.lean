-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_random_looking
-- name    : GraphIsoTesting.FixedGraph.random_looking
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:16.23762+00:00
-- url     : https://prove2.me/theorems/8a49a4b7-19b4-4419-9c8b-a0c40f8ad176
-- title:
--   Claim 2.1 — Random looking
-- statement:
--   Let $A$ be a binary $m\times k$ matrix and let $q$ be a natural number. Suppose every set of at most $q$ rows is linearly independent. For every randomized adaptive algorithm $T$ making at most $q$ coordinate queries, the ordered transcript distributions agree:
--
--   $$\mathcal L(\operatorname{transcript}(T,Ax))=
--   \mathcal L(\operatorname{transcript}(T,b)),\qquad
--   x\sim\operatorname{Unif}(\mathbb F_2^k),\quad b\sim\operatorname{Unif}(\mathbb F_2^m).$$
--
--   The input and tester randomness are independent. The statement permits repeated queries, early halting, and arbitrary internal computation. No sparsity or rank condition is added. This is the indistinguishability result used for image-membership hardness.
--
--   Differences from the source:
--   - encoding: finite binary vectors, adaptive algorithms, and transcript distributions → ZMod 2 vectors and PMF laws of actual ordered query/answer tree executions; reason: finite response trees encode arbitrary adaptive randomized algorithms with the stated maximum query cap, including repeats and early halts
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 5, Claim 2.1

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_BinarySystems

namespace GraphIsoTesting.FixedGraph

theorem random_looking {m k q : ℕ} (A : BinaryMatrix m k)
    (hrows : IndependentRowsUpTo A (q : ℝ))
    (T : RandomizedTester (Fin m) Bit q) :
    transcriptLaw T (PMF.uniformOfFintype (Fin k → Bit)) (fun x => A.mulVec x) =
      transcriptLaw T (PMF.uniformOfFintype (Fin m → Bit)) (fun b => b) := by sorry

end GraphIsoTesting.FixedGraph
