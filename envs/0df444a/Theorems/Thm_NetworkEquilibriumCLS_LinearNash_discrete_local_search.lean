-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_discrete_local_search
-- name    : NetworkEquilibriumCLS.LinearNash.discrete_local_search
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:56.791793+00:00
-- url     : https://prove2.me/theorems/bf50fd33-68e2-49a0-8e67-b0407c400dc2
-- title:
--   Lemma 3.1 — quadratic KKT reduces to discrete local search
-- statement:
--   For every explicitly supplied rational quadratic objective p on a positive-dimensional unit box, a discrete local-search instance can be constructed in polynomial time, with a polynomial-time decoder satisfying
--
--   $$v\text{ locally optimal}\ \Longrightarrow\ D(p,v)\text{ is an exact KKT point of }p.$$
--
--   The formal statement uses the standard Boolean-circuit LocalOpt representation, whose potential is an integer and whose neighbor function supplies an improving move whenever one exists. Both the instance map and the decoder are actual uniform machine computations, and the conclusion covers every local optimum. This is a discrete alternative for recovering an exact continuous solution; it does not restrict the KKT target to the grid.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: a discrete local search instance → the published Boolean-circuit LocalOpt instance with all bit assignments feasible; reason: the source proof establishes polynomial-time neighborhood and integer-objective evaluation, which yield this standard PLS circuit representation without enumerating grid points
--   - generalization: an instance of Quadratic-KKT under the standing assumption |Q_ii| ≤ 1 of §2.1 → every symmetric rational Q, without the diagonal normalization; reason: the source assumes the normalization only after positive rescaling, which preserves exact KKT points and scales ε-KKT tolerances by the same positive factor; restricting to normalized Q recovers the source statement
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.8 (PDF 9), Lemma 3.1.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_BooleanSearch

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem discrete_local_search :
    SearchReduces quadraticSearch ConstrSOSP.LocalOpt := by sorry

end NetworkEquilibriumCLS.LinearNash
