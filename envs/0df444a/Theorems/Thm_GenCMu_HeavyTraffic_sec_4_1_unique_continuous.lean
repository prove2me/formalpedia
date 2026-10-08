-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_sec_4_1_unique_continuous
-- name    : GenCMu.HeavyTraffic.sec_4_1_unique_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:42.449302+00:00
-- url     : https://prove2.me/theorems/3c975538-e48b-4cb1-9314-1268e5021d8c
-- title:
--   §4.1, after (43) — under strict convexity, (43) has a unique solution $g\circ y(t)$, continuous in $t$
-- statement:
--   Let $d \ge 1$, let $\lambda, \rho : [0,1] \to (0,\infty)^d$ be continuous, let each $C^*_k$ be strictly convex, continuous and nondecreasing on $[0,\infty)$, and let $y : [0,1] \to [0,\infty)$ be continuous. Then for every $t \in [0,1]$ the problem
--   $$\min\Big\{\sum_{k=1}^d \lambda_k(t)\,C^*_k\Big(\frac{x_k}{\rho_k(t)}\Big) : x \in \mathbb R^d_+,\ \sum_k x_k = y(t)\Big\} \qquad (43)$$
--   has exactly one solution $g\circ y(t)$, and $t \mapsto g\circ y(t)$ is continuous on $[0,1]$.
--
--   This defines the map $g$ of the lower bound (45) and of Proposition 7.
--
--   **Formalization Note** The paper states uniqueness and continuity for "$C^*$ convex increasing". That is not enough: with $d = 2$, $C^*_k(x) = x$, $\lambda = \rho = 1$, every point of $\Omega$ is optimal. We state the claim under strict convexity, which Assumption 3 provides and Proposition 7 uses. The statement is for general continuous positive rates; the paper's case is $\lambda(t)$, $\rho(t)$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), §4.1, after (43), p. 820

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- §4.1, after (43) (p. 820), under strict convexity: for continuous positive rates and a continuous
nonnegative total `y`, problem (43) has a unique solution `g ∘ y(t)` for every `t ∈ [0, 1]`, and
`t ↦ g ∘ y(t)` is continuous. -/
theorem sec_4_1_unique_continuous {d : ℕ} (hd : 0 < d) (lam rho : ℝ → Fin d → ℝ)
    (Cs : Fin d → ℝ → ℝ)
    (hlam_cont : ContinuousOn lam (Set.Icc 0 1)) (hrho_cont : ContinuousOn rho (Set.Icc 0 1))
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k, 0 < lam t k)
    (hrho : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k, 0 < rho t k)
    (hstrict : ∀ k, StrictConvexOn ℝ (Set.Ici 0) (Cs k))
    (hcont : ∀ k, ContinuousOn (Cs k) (Set.Ici 0))
    (hmono : ∀ k, MonotoneOn (Cs k) (Set.Ici 0))
    (y : ℝ → ℝ) (hy : ContinuousOn y (Set.Icc 0 1)) (hy0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ y t) :
    ∃ G : ℝ → Fin d → ℝ, ContinuousOn G (Set.Icc 0 1) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, IsMin43 (lam t) (rho t) Cs (y t) (G t) ∧
        ∀ x : Fin d → ℝ, IsMin43 (lam t) (rho t) Cs (y t) x → x = G t := by sorry
end GenCMu.HeavyTraffic
