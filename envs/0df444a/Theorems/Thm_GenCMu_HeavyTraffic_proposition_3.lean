-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_3
-- name    : GenCMu.HeavyTraffic.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:17.336916+00:00
-- url     : https://prove2.me/theorems/65054bdb-82a4-4ce5-b231-3a9a4d40415b
-- title:
--   Proposition 3 (LLN) — $\mu_k\tilde W^n_k - \tilde N^n_k \to 0$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumption 1 and let $T^n$ be feasible work-conserving policies. Then, uniformly in $t \in [0,1]$ and $k$,
--   $$\mu_k\big(R^*_k(t)\big)\,\tilde W^n_k(t) - \tilde N^n_k(t) \to 0 \qquad (36).$$
--
--   The class workload is asymptotically the class headcount times the mean service requirement $1/\mu_k$: a law of large numbers for the service times of the jobs present.
--
--   **Formalization Note** The paper writes $\mu_k$; its proof ((80)–(84), p. 828) produces the factor $\bar V^{*\prime}_k(\bar A^n_k(t))^{-1} \to \mu_k(R^*_k(t))$, and we state that. The two readings coincide when the service rate is constant.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), p. 819, Proposition 3 (LLN), (36)

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 3 (LLN), (36) (p. 819): `μ_k W̃ⁿ_k − Ñⁿ_k → 0` uniformly on `[0, 1]`, with `μ_k`
read at `R*_k(t)`. -/
theorem proposition_3 {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n)) :
    TendstoUniformlyOn (fun (n : ℕ) t k => M.muR k t * H.Wt T n t k - H.Nt T n t k)
      (fun _ _ => 0) atTop (Set.Icc 0 1) := by sorry
end GenCMu.HeavyTraffic
