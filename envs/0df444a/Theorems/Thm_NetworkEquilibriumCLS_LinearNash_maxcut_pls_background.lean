-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_maxcut_pls_background
-- name    : NetworkEquilibriumCLS.LinearNash.maxcut_pls_background
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:46.26402+00:00
-- url     : https://prove2.me/theorems/551279e8-d933-4951-a113-bcb44b6b85c3
-- title:
--   Background — Corollary 5.12, full MAX CUT classification
-- statement:
--   For an explicitly given simple undirected graph with positive binary integer edge weights, a local maximum cut is a partition for which moving any one vertex does not increase cut weight. The exact search problem has the classification
--
--   $$\mathrm{Local\text{-}MAX\ CUT}\text{ is PLS-complete}.$$
--
--   Membership includes totality, polynomial-size bit answers and polynomial verification. Hardness ranges over every problem in the fixed LocalOpt-based PLS class and uses polynomial-time instance and every-answer decoder maps. This is the complete MAX CUT clause of the cited corollary; its independent clauses about other optimization problems are outside this mission. It supplies the external reduction used in the proof of Lemma 3.2.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: a graph with positive edge weights → upper-triangular natural weights, zero denoting absent edges; redundant lower triangle ignored; reason: every represented instance denotes such a graph and every source graph is represented; the feasible cuts and all flip comparisons are unchanged
-- source:
--   Schäffer and Yannakakis, Simple Local Search Problems that are Hard to Solve, SIAM J. Comput. 20(1), 56–87 (1991), Definition 2.8, p.61, and Corollary 5.12, MAX CUT clause, p.83, https://doi.org/10.1137/0220004; invoked by submission p.9 (PDF 10), proof of Lemma 3.2.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_LocalMaxCut

namespace NetworkEquilibriumCLS.LinearNash

/-- Supporting background result explicitly invoked by the source proof. -/
theorem maxcut_pls_background : PLSComplete maxcutSearch := by sorry

end NetworkEquilibriumCLS.LinearNash
