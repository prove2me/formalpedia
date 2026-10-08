-- Prove2me | Theorems.Thm_NonlinSSD_Discrete_kkt_under_slater
-- name    : NonlinSSD.Discrete.kkt_under_slater
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:03:33.420578+00:00
-- url     : https://prove2.me/theorems/412a8bb9-a8e0-4b60-8b08-e7d852295e4c
-- title:
--   p. 16–17, Slater condition — Kuhn–Tucker multipliers μ ≥ 0, θ ≥ 0 exist for problem (38)–(41)
-- statement:
--   Consider problem (38)–(41) under the standing assumptions: probabilities $p_j \ge 0$ with $\sum_j p_j = 1$, a convex set $Z \subseteq \mathbb R^N$, and functions $h_j$, $g_{ij}$ concave on $\mathbb R^N$. Assume the Slater condition: there exist $\tilde z \in \operatorname{relint} Z$ and $\tilde X$ with $\tilde x_{ik} < g_{ik}(\tilde z)$ for all $i, k$ and with the dominance constraints (39) satisfied. If $(\hat z, \hat X)$ is an optimal solution of (38)–(41), then there exist $\mu_{ik} \ge 0$ and $\theta_{ij} \ge 0$ such that
--
--   1. $(\hat z, \hat X)$ maximizes the standard Lagrangian over $Z \times \mathbb R^{mn}$:
--   $$\Lambda(z, X, \mu, \theta) \le \Lambda(\hat z, \hat X, \mu, \theta) \quad \text{for all } z \in Z,\ X \in \mathbb R^{mn};$$
--   2. complementarity holds for the dominance constraints: $\mu_{ik}\big[\sum_j p_j (y_{ik} - y_{ij})_+ - \sum_j p_j (y_{ik} - \hat x_{ij})_+\big] = 0$ for all $i, k$;
--   3. complementarity holds for the splitting constraints: $\theta_{ij}\big(g_{ij}(\hat z) - \hat x_{ij}\big) = 0$ for all $i, j$.
--
--   The paper obtains this from Rockafellar, *Convex Analysis*, Thm. 28.2 and Cor. 28.3.1: the left-hand sides of (39) are convex polyhedral functions of $x$, so those constraints need not hold strictly at the Slater point.
--
--   **Formalization Note.** The relative interior is `intrinsicInterior ℝ Z`, not the topological interior, so lower-dimensional sets $Z$ (such as a simplex in $\mathbb R^N$) are allowed. Continuity of $h_j$, $g_{ij}$ (part of the paper's standing assumption on p. 2) is not stated, because a finite concave function on $\mathbb R^N$ is continuous. In $\Lambda$ the multiplier $\theta_{ij}$ multiplies $p_j(g_{ij}(z) - x_{ij})$, as printed on p. 17.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 16, Slater condition (citing Rockafellar Thm. 28.2), and p. 17, proof of Theorem 6 (citing Rockafellar Cor. 28.3.1); standing assumptions p. 2

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

namespace NonlinSSD.Discrete

theorem kkt_under_slater {m n N : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (Z : Set (Fin N → ℝ)) (hZ : Convex ℝ Z)
    (h : Fin n → (Fin N → ℝ) → ℝ) (hh : ∀ j, ConcaveOn ℝ Set.univ (h j))
    (g : Fin m → Fin n → (Fin N → ℝ) → ℝ) (hg : ∀ i j, ConcaveOn ℝ Set.univ (g i j))
    (y : Fin m → Fin n → ℝ) (hS : SlaterCondition p Z g y)
    (zh : Fin N → ℝ) (Xh : Fin m → Fin n → ℝ) (hopt : IsOptimal p Z h g y zh Xh) :
    ∃ μ θ : Fin m → Fin n → ℝ, (∀ i k, 0 ≤ μ i k) ∧ (∀ i j, 0 ≤ θ i j) ∧
      (∀ z ∈ Z, ∀ X : Fin m → Fin n → ℝ,
        stdLagrangian p h g y z X μ θ ≤ stdLagrangian p h g y zh Xh μ θ) ∧
      (∀ i k, μ i k * ((∑ j, p j * max (y i k - y i j) 0) -
        ∑ j, p j * max (y i k - Xh i j) 0) = 0) ∧
      (∀ i j, θ i j * (g i j zh - Xh i j) = 0) := by sorry

end NonlinSSD.Discrete
