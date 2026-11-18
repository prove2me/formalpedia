-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_local_program_upper_bound
-- name    : NearlyOptimalPPR.Computation.local_program_upper_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T02:15:33.443347+00:00
-- url     : https://prove2.me/theorems/20bb4884-6ba9-4267-a79b-27c7c34a436f
-- title:
--   Theorem 1.2 — uniform local-program upper bound
-- statement:
--   Fix the exact-SDDM primitive model, with its positive solve constant and fixed nonnegative integer logarithmic exponent. There exist one admissible finite scalar/query program and positive constants $C,c$, chosen before the graph, seed and real parameters, such that for every finite simple undirected graph, seed $s$, $0<\alpha<1$ and $0<\varepsilon\le1$, the program terminates almost surely with a nonnegative explicit sparse output satisfying the ACL error guarantee. An isolated source is returned exactly.
--
--   Its charged work is measurable and satisfies, with $K=1/\varepsilon$,
--
--   $$
--   \mathbb E W\le CK\exp\!\left(c\sqrt{\log(2K)\log\log(4K)}\right).
--   $$
--
--   For every $\eta>0$, the displayed envelope is at most $K^{1+\eta}$ for all sufficiently large $K$, uniformly over graphs and teleportation parameters. The program receives only the seed and the two real parameters, accesses degrees and neighbors locally, and must implement parameter preparation with its actual charged instructions. The primitive solves only an already prepared sparse SDDM system; assembly, propagation and emitted output remain charged separately.
--
--   This is the algorithmic upper-bound branch of Theorem 1.2. Its explicit-output lower bound is an independent theorem.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Theorem 1.2 p.2, exact-SDDM convention §2 p.4, Lemma 4.5 pp.18–19, Algorithms 6–9 pp.20–22.

import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace NearlyOptimalPPR.Computation

theorem local_program_upper_bound (m : SolveModel) :
    ∃ (p : Program) (C c : ℝ), admissible p ∧ 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 →
          successful m p g s α ε ∧
          Measurable (executionWork m p g s α ε) ∧
          expectedWork m p g s α ε ≤ ENNReal.ofReal (envelope C c ε)) ∧
      subpolynomialEnvelope C c := by sorry

end NearlyOptimalPPR.Computation
