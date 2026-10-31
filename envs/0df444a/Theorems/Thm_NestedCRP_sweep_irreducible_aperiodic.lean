-- Prove2me | Theorems.Thm_NestedCRP_sweep_irreducible_aperiodic
-- name    : NestedCRP.sweep_irreducible_aperiodic
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:51.432721+00:00
-- url     : https://prove2.me/theorems/1b4eab48-0536-40bc-aec1-c08a9602bedf
-- title:
--   The sweep is irreducible and aperiodic
-- statement:
--   For all hyperparameters and every corpus over a vocabulary of size $V\ge1$, the sweep of the sampler is irreducible and aperiodic on the countable state space of trees and level allocations.
--
--   The paper does not state this, but its claim that the algorithm is guaranteed to converge in the limit needs it. It is the hypothesis, with positive recurrence, of the convergence theorem for countable chains.
--
--   Differences from the source:
--   - reading: "this algorithm is guaranteed to converge in the limit", no chain property stated → the sweep is irreducible and aperiodic; reason: this is a step the sentence needs, and every conditional weight is positive
--   - encoding: a vocabulary of V words, nonempty implicitly → [NeZero V], that is V ≥ 1; reason: nondegeneracy only: at V = 0 the symmetric Dirichlet on the empty simplex is undefined and the Γ(Vη) = Γ(0) factors of the path weights are poles; no instance of the source is excluded
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.3, p.7:17

import Mathlib
import Definitions.Def_mm_countable
import Definitions.Def_NestedCRP_sweep
open MarkovMixing

namespace NestedCRP

/-- The sweep is irreducible and aperiodic on the countable state space. The paper needs this for
"guaranteed to converge in the limit" and does not prove it. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.3, p.7:17. -/
theorem sweep_irreducible_aperiodic {V D : ℕ} [NeZero V] (H : Hyper) (C : Corpus V D) :
    IrreducibleC (sweep H C) ∧ AperiodicC (sweep H C) := by sorry

end NestedCRP
