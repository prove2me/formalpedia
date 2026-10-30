-- Prove2me | Theorems.Thm_LSWNewArcAudit_NewArc_lemma79_full
-- name    : LSWNewArcAudit.NewArc.lemma79_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:43:32.851705+00:00
-- url     : https://prove2.me/theorems/0c67edc8-4f25-4788-aa7e-6f7da7259cb4
-- title:
--   Lemma 79 — valid new arc with linear evaluations and quadratic additional work
-- statement:
--   For every fixed integer $c\ge1$, there exist one finite exact arithmetic oracle program $P_c$ and positive constants $C_Q(c),C_T(c)$, independent of every input instance below.
--
--   Let $f:2^V\to\mathbb Z$ be submodular with $f(\varnothing)=0$, let $A$ be an acyclic graph on the finite ground set $V$ of size $n$, and let $p\in V$. Supply $m\le cn$ consistent BFS arrays $y^{(k)}$ and their defining permutations, and arbitrary real weights $\lambda_k\ge0$ summing to one. Write $y=\sum_k\lambda_k y^{(k)}$, and assume that $y$ has both a strictly positive and a strictly negative coordinate. If
--
--   $$f(R(p))-f(R(p)\setminus\{p\})>n^4\max_{j\in V}y_j,$$
--
--   then the execution of $P_c$, on exactly those supplied arrays and the value oracle for $f$, terminates and returns some $q\in V$ for which
--
--   $$q\notin R(p),\qquad \forall S\in\operatorname{argmin}_{T\in\mathcal F_A} f(T),\quad p\in S\Longrightarrow q\in S.$$
--
--   That very execution satisfies
--
--   $$Q\le C_Q(c)n,\qquad W\le C_T(c)n^2,$$
--
--   where $Q$ counts evaluations and $W$ counts additional elementary instructions, including data access, arithmetic, graph work, bitmap changes, query dispatch and halting. Only the query instruction accesses $f$. There is no dependence on the magnitudes of its integer values, no restriction to rational or strictly positive weights, and no dimension threshold. This supplies the computational content absent from the existing existence-only theorem.
--
--   Differences from the source:
--   - reading: O(n EO) oracle calls and O(n²) time in the wording of Lemma 79 → O(n) evaluations and O(n²) additional elementary work on the same terminating execution; reason: pp. 85–86 explicitly count O(n) evaluations, and §15.3.3 p. 95 gives total time O(n EO+n²)
--   - encoding: O(n) supplied BFSs and asymptotic computational bounds → for every fixed integer c≥1, one finite program and positive natural constants chosen before every instance with m≤cn, bounding queries by C_Q n and work by C_T n²; reason: this makes the support constant and uniformity explicit, permits rounding cost constants upward, and excludes no small admissible dimension
--   - encoding: given BFS vectors, real convex coefficients and defining permutations in the arithmetic/evaluation-oracle model → typed explicit input tapes and exact real/integer RAM execution with charged loads, scalar operations, bitmap access, queries and halting, using rational program literals; reason: this makes the computational model precise without restricting real input weights or integer function magnitudes, supplying advice, or charging arbitrary counters
--   - encoding: V=[n], nondegeneracy, consistency and descendants including p → Fin n with NeZero n, the published mixed-sign and position-map predicates, and reflexive-transitive reachability; reason: a supplied p already forces nonemptiness; position labels are reindexed and every source instance and minimizer is retained
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2 (5 Nov 2015), https://arxiv.org/pdf/1508.04874v2, §15.2.2, Lemma 79 (new arc), printed/PDF p. 84, proof pp. 85–86; §15.3.3 p. 95 for total-time reading; standing assumptions §13.1 p. 74, §13.3 pp. 76–77, §15.2.1 pp. 81–82.

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_RepresentedInput

namespace LSWNewArcAudit.NewArc

open LSWCuttingPlane.SFMArcs

/-- Lee--Sidford--Wong, arXiv:1508.04874v2, Lemma 79, p. 84,
proof pp. 85--86: the full uniform algorithmic statement. A single finite
oracle program and positive constants are chosen before every instance.
The same deterministic execution halts with a valid q outside reflexive R(p)
and has at most C_Q n evaluations and C_T n² additional elementary steps.
For each fixed support constant c, all m ≤ c n and all real convex weights
are covered. There is no threshold on n or bound on integer oracle magnitudes. -/
theorem lemma79_full :
    ∀ c : ℕ, 1 ≤ c →
    ∃ program : OracleProgram, LiteralProgram program ∧
    ∃ C_Q C_T : ℕ, 0 < C_Q ∧ 0 < C_T ∧
    ∀ (n : ℕ) [NeZero n] (m : ℕ) (I : ArcInput n m)
      (f : Finset (Fin n) → ℤ),
      Submodular f → f ∅ = 0 → Acyclic (inputArcs I) →
      m ≤ c * n → RepresentedCombination f I →
      NonDegenerate (inputVector I) →
      (n : ℝ) ^ 4 * ymax (inputVector I) < (upper f (inputArcs I) I.point : ℝ) →
      ∃ (steps : ℕ) (q : Fin n),
        let result := oracleRun program f (inputMemory I) steps
        result.output = some (q.val : ℤ) ∧
        q ∉ R (inputArcs I) I.point ∧
        (∀ S : Finset (Fin n), IsMinimizer (inputArcs I) f S →
          I.point ∈ S → q ∈ S) ∧
        result.queries ≤ C_Q * n ∧ result.work ≤ C_T * n ^ 2 := by sorry

end LSWNewArcAudit.NewArc
