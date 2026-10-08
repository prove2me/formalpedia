-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_5
-- name    : GenCMu.HeavyTraffic.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:45.790626+00:00
-- url     : https://prove2.me/theorems/f82416a1-0dd1-4f27-a414-63d048cf632d
-- title:
--   Proposition 5 — for converging policies, $\lambda\tilde\tau^*=\tilde N^*$, $\mu\tilde W^*=\tilde N^*$, and $\tilde J^n\to\sum_k\int\lambda_kC^*_k(\tilde\tau^*_k)\,dt$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumptions 1 and 2 and let $T^n$ be feasible work-conserving policies such that $\tilde T^n$ converges uniformly on $[0,1]$. Then there are functions $\tilde W^*, \tilde N^*, \tilde\tau^*$ with $\tilde W^n \to \tilde W^*$ and $\tilde N^n \to \tilde N^*$ uniformly on $[0,1]$, $\tilde\tau^n \to \tilde\tau^*$ uniformly on $[0,1]$, and
--   $$\lambda\tilde\tau^* = \tilde N^* \ \ (40), \qquad \mu\tilde W^* = \tilde N^* \ \ (41), \qquad \tilde J^n(t) \to \sum_k\int_0^t \lambda_k(s)C^*_k\big(\tilde\tau^*_k(s)\big)\,ds \ \ (42),$$
--   the last uniformly in $t \in [0,1]$.
--
--   When the policies converge there is a limiting system in which Little's law holds at each time, and the asymptotic cost is the integral of the instantaneous class costs.
--
--   **Formalization Note** $\mu$ in (41) is $\mu_k(R^*_k(t))$. (40), (42), and delay convergence hold on the paper's full $[0,1]$ under the explicit post-horizon allocation condition.
--
--   The added `PostHorizonRegular` hypothesis requires $T^n_k(n+s\sqrt n)-T^n_k(n)=\rho_k(1)s\sqrt n+o(\sqrt n)$ uniformly for bounded $s\ge0$. It supplies the service behavior that the paper leaves unspecified after $n$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), p. 819, Proposition 5, (40)–(42)

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 5 (p. 819): if `T̃ⁿ` converges, then `W̃ⁿ, Ñⁿ, τ̃ⁿ` converge on `[0,1]`,
the limits satisfy (40) `λτ̃* = Ñ*` and (41) `μW̃* = Ñ*`, and (42)
`J̃ⁿ → Σ_k ∫ λ_k C*_k(τ̃*_k) dt`. -/
theorem proposition_5 {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (Cs : Fin d → ℝ → ℝ) (h2 : CostConvergence H Cs) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n)) (hpost : PostHorizonRegular H M T)
    (hconv : ∃ Ts : ℝ → Fin d → ℝ, TendstoUniformlyOn (H.Ttil T) Ts atTop (Set.Icc 0 1)) :
    ∃ Ws Ns τs : ℝ → Fin d → ℝ,
      TendstoUniformlyOn (H.Wt T) Ws atTop (Set.Icc 0 1) ∧
      TendstoUniformlyOn (H.Nt T) Ns atTop (Set.Icc 0 1) ∧
      TendstoUniformlyOn (H.taut T) τs atTop (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k, M.lam k t * τs t k = Ns t k) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k, M.muR k t * Ws t k = Ns t k) ∧
      TendstoUniformlyOn (H.Jt T)
        (fun t => ∑ k, ∫ s in (0 : ℝ)..t, M.lam k s * Cs k (τs s k)) atTop (Set.Icc 0 1) := by sorry
end GenCMu.HeavyTraffic
