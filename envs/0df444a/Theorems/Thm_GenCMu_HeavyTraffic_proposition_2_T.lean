-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_T
-- name    : GenCMu.HeavyTraffic.proposition_2_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:26.791125+00:00
-- url     : https://prove2.me/theorems/930dd749-1ca4-4bec-8b22-492f85aacc64
-- title:
--   Proposition 2, (22) and (27) — the first-order allocation $T^n(n\cdot)/n$ converges to $R^*$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumption 1 and let $T^n$ be a feasible work-conserving policy of the $n$th system for each $n$. Then, uniformly in $t \in [0,1]$ and $k$,
--   $$\frac{T^n_k(nt)}{n} \to R^*_k(t) = (\bar S^*_k)^{-1}\big(\bar A^*_k(t)\big).$$
--
--   To first order every work-conserving policy allocates the server identically: class $k$ receives the time its offered work requires. Policies differ only at the diffusion scale $n^{1/2}$.
--
--   **Formalization Note** The paper writes $T^n(nt) = n\bar T^n(t) + n^{1/2}\tilde T^n(t) + o(n^{1/2})$ (22) and $\bar T^n \to R^*$ (27), with $\bar T^n = R^n$ (75); we state the resulting convergence of $T^n(n\cdot)/n$. The paper states it "for any scheduling policy"; we state it for feasible work-conserving policies (see `GenCMu.HeavyTraffic.Model`).
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), pp. 817–818, Proposition 2, (22), (27); Appendix, (75), p. 827

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 2, (22) with (27) (pp. 817–818): for every sequence of feasible work-conserving
policies, the first-order allocation `Tⁿ(n·)/n` converges uniformly on `[0, 1]` to `R*`. -/
theorem proposition_2_T {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n)) :
    TendstoUniformlyOn (fun (n : ℕ) t k => T n (n * t) k / n) (fun t k => M.Rstar k t) atTop
      (Set.Icc 0 1) := by sorry
end GenCMu.HeavyTraffic
