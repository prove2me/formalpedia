-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_8_1
-- name    : HypRecov.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:27:18.31596+00:00
-- url     : https://prove2.me/theorems/6d7b9cf8-b678-468f-b93f-3a03c8235919
-- title:
--   Theorem 8.1 — reconstruction of $d$-cut-degenerate hypergraphs
-- statement:
--   Let $n\ge r\ge2$, $d\ge1$, $0<\eta<1/2$, and set
--   $$q=\min\{r,1+\lceil\log_2(d+1)\rceil\}.$$
--   There is one uniform randomized one-pass additive sketch that, from every fixed valid integer $q$-fragment stream independent of its coins, recovers every original edge with its complete membership whenever the terminal hypergraph is simple, $r$-uniform and $d$-cut-degenerate. Recovery succeeds with probability at least $1-\eta$.
--
--   The state, random description, retained output and decoding workspace use $\widetilde O(nrd)$ bits. Initialization, update, state subtraction and decoding are polynomial in $n,r,d,\log(1/\eta)$, with update time also polynomial in the increment's bit length. If $n\ge2r$, this is the least possible observation order even without resource restrictions.
--
--   Differences from the source:
--   - encoding: one-pass additive sketch with $\widetilde O(nrd)$ space and polynomial time → one set of TM2 machines with absolute constants chosen before all parameters, an order-independent state function, additive updates, state subtraction, and all-stack step/space bounds; reason: this is the published base mission's moderated machine interpretation of the same sketch and resource language
--   - encoding: recovery is promised only for $d$-cut-degenerate terminal hypergraphs → correctness is an implication from `IsCutDegenerate E d`, while all machines remain resource-bounded outside the promise; reason: this is the direct predicate encoding of a promise problem
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 8.1, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_HypRecov_qid
import Definitions.Def_HypRecov_SketchGuarantee
import Definitions.Def_HypRecov_Supplement_QuerySketchGuarantee

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem 8.1 (Cut-degenerate reconstruction from anonymous projections).** Zhang, Chen, Shen,
*Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256
719dcfff…), Theorem 8.1, p.20 (PDF p.21).

One uniform randomized additive sketch at order `min{r,1+ceil(log₂(d+1))}` reconstructs every
original edge of every simple `r`-uniform `d`-cut-degenerate hypergraph, with complete memberships,
from each fixed valid stream with failure at most `eta`.  Its state, random description, retained
output and decoding workspace use `O-tilde(nrd)` bits, and its machines have uniform polynomial
time bounds including the increment's binary length.  If `n ≥ 2r`, the order is the least possible
even without resource restrictions.

**Formalization Note.** `SketchGuarantee` is the published all-stack TM2 model and makes the state a
function of the terminal projection vector and one fixed tape, so repeated peeling receives no fresh
randomness.  Outside the promised cut-degenerate class the correctness predicate is vacuous, while
machine time and space remain capped. -/
theorem theorem_8_1 :
    ∃ (A : HypRecov.LinearSketch) (C c : ℕ),
      ∀ (n r d : ℕ) (eta : ℝ), r ≤ n → 2 ≤ r → 1 ≤ d → 0 < eta → eta < 1 / 2 →
        HypRecov.SketchGuarantee A C c n r (d + 1) (n * r * d) eta
            (HypRecov.qid r (d + 1))
            (fun E out => IsCutDegenerate E d → FullEdgeOutput E out) ∧
        (2 * r ≤ n →
          IsLeast {q : ℕ | 1 ≤ q ∧ q ≤ r ∧ DeterminesCutDegenerate n r d q}
            (HypRecov.qid r (d + 1)))
    := by sorry

end HypRecov.Supplement
