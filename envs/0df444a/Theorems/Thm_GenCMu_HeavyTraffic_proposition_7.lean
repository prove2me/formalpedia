-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_7
-- name    : GenCMu.HeavyTraffic.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:44.942003+00:00
-- url     : https://prove2.me/theorems/bc930af4-a113-4ce0-9579-43c2699c54fc
-- title:
--   Proposition 7 — policies equalizing $\mu_kc^*_k(\tilde W^n_k/\rho_k)$ attain the lower bound: $\tilde J^n\to\tilde J^*$, $\tilde\tau^n\to g\circ\tilde W^*_+/\rho$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumptions 1, 2 and 3, and let $T^n$ be feasible work-conserving policies such that, uniformly in $t \in [0,1]$,
--   $$\max_{1\le k,l\le d}\Big|\mu_k c^*_k\Big(\frac{\tilde W^n_k(t)}{\rho_k(t)}\Big) - \mu_l c^*_l\Big(\frac{\tilde W^n_l(t)}{\rho_l(t)}\Big)\Big| \to 0 \qquad (51).$$
--   Then the policies are asymptotically optimal: uniformly in $t \in [0,1]$,
--   $$\tilde J^n(t) \to \tilde J^*(t) \qquad (52), \qquad \tilde\tau^n(t) \to \tilde\tau^*(t) = \frac{g\circ\tilde W^*_+(t)}{\rho(t)} \qquad (53),$$
--   where $\tilde J^*$ is the lower bound of Proposition 6 and $g\circ\tilde W^*_+(t)$ is the solution of (43) at $y = \tilde W^*_+(t)$.
--
--   A policy that keeps the indices $\mu_k c^*_k(W_k/\rho_k)$ of all classes asymptotically equal (the generalized $c\mu$ rule, serving the class with the largest index) attains the lower bound of Proposition 6 at every time simultaneously; with linear costs it reduces to the classical $c\mu$ rule.
--
--   **Formalization Note** Here $\mu_k$ is $\mu_k(R^*_k(t))$ and $\rho_k = \lambda_k/\mu_k$. (53) is stated for every $\tilde\tau^*$ such that $\rho(t)\tilde\tau^*(t)$ solves (43) at $\tilde W^*_+(t)$ for all $t\in[0,1]$; under Assumption 3 that solution is unique (see `GenCMu.HeavyTraffic.sec_4_1_unique_continuous`), so this is the paper's $g\circ\tilde W^*_+/\rho$ without a choice function. The paper states (52)–(53) uniformly on $[0,1]$; the explicit post-horizon allocation condition controls the post-horizon delay of final arrivals. Assumption 3's interior clause is imposed where $\tilde W^*_+(t) > 0$. The policies are feasible, work conserving and class-FIFO (see `GenCMu.HeavyTraffic.Model`). "Asymptotically optimal" refers to the lower bound of Proposition 6, which is a separate item and not part of this statement.
--
--   The added `PostHorizonRegular` hypothesis requires $T^n_k(n+s\sqrt n)-T^n_k(n)=\rho_k(1)s\sqrt n+o(\sqrt n)$ uniformly for bounded $s\ge0$. It supplies the service behavior that the paper leaves unspecified after $n$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), §4.2, p. 822, Proposition 7, (51)–(53)

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 7 (p. 822): under Assumptions 1, 2 and 3, a sequence of feasible work-conserving
policies satisfying (51) is asymptotically optimal: (52) `J̃ⁿ → J̃*` and (53)
`τ̃ⁿ → τ̃* = g ∘ W̃*_+ / ρ`, uniformly on `[0,1]`. -/
theorem proposition_7 {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (Cs : Fin d → ℝ → ℝ) (h2 : CostConvergence H Cs)
    (h3 : CostRegularity M Cs) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n))
    (hpost : PostHorizonRegular H M T)
    (h51 : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k l : Fin d,
      |M.muR k t * mc Cs k (H.Wt T n t k / M.rho k t)
        - M.muR l t * mc Cs l (H.Wt T n t l / M.rho l t)| ≤ ε) :
    TendstoUniformlyOn (H.Jt T) (Jstar M Cs) atTop (Set.Icc 0 1) ∧
    ∀ τs : ℝ → Fin d → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsMin43 (fun k => M.lam k t) (fun k => M.rho k t) Cs (Wstar M t)
        (fun k => M.rho k t * τs t k)) →
      TendstoUniformlyOn (H.taut T) τs atTop (Set.Icc 0 1) := by sorry
end GenCMu.HeavyTraffic
