-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_eq_46_50_kuhn_tucker
-- name    : GenCMu.HeavyTraffic.eq_46_50_kuhn_tucker
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:51.835348+00:00
-- url     : https://prove2.me/theorems/0eea6bba-09c8-431f-9b21-4bb6d7f154a4
-- title:
--   §4.2, (46)–(50) — the Kuhn–Tucker conditions characterize the solutions of (43); interior solutions equalize $\mu_kc^*_k(x_k/\rho_k)$
-- statement:
--   Fix $\lambda_k > 0$ and $\rho_k > 0$, put $\mu_k = \lambda_k/\rho_k$, let each $C^*_k$ be convex and continuously differentiable on $[0,\infty)$ with derivative $c^*_k$ (right derivative at $0$), and let $x \in \mathbb R^d_+$ with $\sum_k x_k = y$. Then $x$ solves (43) if and only if there are $\alpha_0 \in \mathbb R$ and $\alpha_k \ge 0$ with
--   $$\mu_k\,c^*_k\Big(\frac{x_k}{\rho_k}\Big) - \alpha_k = \alpha_0 \ \ (46), \qquad \alpha_k x_k = 0 \ \ (47) \qquad (1\le k\le d).$$
--   If moreover every $x_k > 0$, then $x$ solves (43) if and only if
--   $$\mu_k\,c^*_k\Big(\frac{x_k}{\rho_k}\Big) = \alpha_0 \quad \text{for all } k \qquad (49)$$
--   for some $\alpha_0 \in \mathbb R$; (48) and (50) are the constraint $\sum_k x_k = y$.
--
--   The optimal split of the total workload equalizes the indices $\mu_k c^*_k(x_k/\rho_k)$, which is what the generalized $c\mu$ rule does dynamically.
--
--   **Formalization Note** The paper states that the Kuhn–Tucker conditions are sufficient; we state both directions (necessity also holds, the constraints being linear). The rates are fixed numbers, the paper's $\lambda(t)$, $\rho(t)$ at a fixed $t$; $\mu_k = \lambda_k/\rho_k$ is the paper's $\mu_k(t)$ read as $\mu_k(R^*_k(t))$, the coefficient produced by differentiating the objective.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), §4.2, (46)–(48), p. 821, and (49)–(50), p. 822

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- §4.2, (46)–(50) (pp. 821–822): for `C*` convex and `𝒞¹` on `[0, ∞)`, a point `x ∈ Ω` solves (43)
iff it satisfies the Kuhn–Tucker conditions (46)–(48) with `μ_k = λ_k/ρ_k`; for an interior `x`
they reduce to (49)–(50). -/
theorem eq_46_50_kuhn_tucker {d : ℕ} (lam rho : Fin d → ℝ) (Cs : Fin d → ℝ → ℝ)
    (hlam : ∀ k, 0 < lam k) (hrho : ∀ k, 0 < rho k)
    (hconv : ∀ k, ConvexOn ℝ (Set.Ici 0) (Cs k)) (hC1 : ∀ k, ContDiffOn ℝ 1 (Cs k) (Set.Ici 0))
    (y : ℝ) (x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = y) :
    (IsMin43 lam rho Cs y x ↔
      ∃ α₀ : ℝ, ∃ α : Fin d → ℝ, (∀ k, 0 ≤ α k) ∧
        (∀ k, lam k / rho k * mc Cs k (x k / rho k) - α k = α₀) ∧ (∀ k, α k * x k = 0)) ∧
    ((∀ k, 0 < x k) →
      (IsMin43 lam rho Cs y x ↔ ∃ α₀ : ℝ, ∀ k, lam k / rho k * mc Cs k (x k / rho k) = α₀)) := by sorry
end GenCMu.HeavyTraffic
