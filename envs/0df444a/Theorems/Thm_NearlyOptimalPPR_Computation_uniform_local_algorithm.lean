-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_uniform_local_algorithm
-- name    : NearlyOptimalPPR.Computation.uniform_local_algorithm
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T02:36:44.554075+00:00
-- url     : https://prove2.me/theorems/90d14f00-4a95-40b5-82d3-e542631c35c8
-- title:
--   Theorem 1.2 — local algorithm with uniform expected work
-- statement:
--   Fix an exact-SDDM primitive model. There exist one admissible local scalar/query program and positive constants $C,c$, fixed before all graph inputs, seeds and parameters, such that every finite simple undirected graph, seed $s$, $0<\alpha<1$ and $0<\varepsilon\le1$ receives an almost-surely terminating nonnegative explicit output with the ACL guarantee. An isolated seed is returned exactly.
--
--   Writing $K=1/\varepsilon$, the expected charged work satisfies
--
--   $$
--   \mathbb E W\le CK\exp\!\left(c\sqrt{\log(2K)\log\log(4K)}\right).
--   $$
--
--   All parameter preparation, graph queries, sparse-system assembly, boundary propagation and output must be implemented by the program's charged instructions. Exact solves operate only on already prepared sparse SDDM systems.
--
--   This is the algorithmic core of the upper bound. Measurability of execution work and the envelope's eventual $K^{1+\eta}$ bound are established separately as general results and combined with this statement in the parent theorem.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Theorem 1.2 p.2; §2 p.4 exact-SDDM model; Lemma 4.5 pp.18–19.

import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace NearlyOptimalPPR.Computation

theorem uniform_local_algorithm (m : SolveModel) :
    ∃ (p : Program) (C c : ℝ), admissible p ∧ 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 →
          successful m p g s α ε ∧
          expectedWork m p g s α ε ≤ ENNReal.ofReal (envelope C c ε)) := by sorry

end NearlyOptimalPPR.Computation
