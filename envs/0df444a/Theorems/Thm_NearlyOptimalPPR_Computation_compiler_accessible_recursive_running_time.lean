-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_compiler_accessible_recursive_running_time
-- name    : NearlyOptimalPPR.Computation.compiler_accessible_recursive_running_time
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:45:41.089672+00:00
-- url     : https://prove2.me/theorems/ed9bcc23-009b-48a3-a8db-627ad6c16e62
-- title:
--   Accessible-depth recursive source computation has the near-linear envelope
-- statement:
--   For every fixed exact-SDDM solve model there are positive constants $C,c$, independent of graph, seed, and input parameters, with the following property. On a nonisolated seed, $0<\alpha\le1/2$, and $0<\varepsilon\le1$, use the depth specified by the charged integer-power preparation search. The canonical recursive source computation terminates after a finite prefix and its charged source work satisfies
--
--   $$W_{\rm src}\le C\varepsilon^{-1}\exp\!\left(c\sqrt{\log(2/\varepsilon)\log\log(4/\varepsilon)}\right).$$
--
--   The displayed envelope is subpolynomial beyond its leading factor: for each $\eta>0$ it is at most $K^{1+\eta}$ for all sufficiently large $K=1/\varepsilon$. This theorem concerns the canonical source computation at the depth realized by parameter preparation; separate simulation theorems transfer the bound to machine instructions.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas4.4–4.5, pp.17–19; accessible integer-power depth used in the charged implementation.

import Definitions.Def_NearlyOptimalPPR_Computation_compiler_runtime
import Definitions.Def_NearlyOptimalPPR_Computation_compiler_buffers
open Finset Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace NearlyOptimalPPR.Computation
open SparseQueue
theorem compiler_accessible_recursive_running_time (m : SolveModel) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ subpolynomialEnvelope C c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α ≤ 1/2 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
        let ℓ := accessibleDepth (1/ε)
        recursiveWork m g s α ε ℓ [] ≤ ENNReal.ofReal (envelope C c ε) ∧
          ∃ t, (recursiveRun m g s α (rootThreshold ε ℓ) ℓ [] t).done=true := by sorry
end NearlyOptimalPPR.Computation
