-- Prove2me | Theorems.Thm_MangasarianFJ_GenFJ_generalized_fritz_john
-- name    : MangasarianFJ.GenFJ.generalized_fritz_john
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:41:22.547993+00:00
-- url     : https://prove2.me/theorems/7e9d3307-a357-4c38-bf6c-819cf5958048
-- title:
--   Generalized Fritz John Necessary Conditions (§2), p. 41 — at a solution of (1.1) there are ū ≥ 0, v̄, (ū, v̄) ≠ 0, satisfying (2.9)–(2.10)
-- statement:
--   Consider the program (1.1): minimize $\theta(x)$ subject to $g_i(x)\le0$, $i\in M=\{1,\dots,m\}$, and $h_j(x)=0$, $j\in K=\{1,\dots,k\}$, where $\theta, g_i, h_j:E^n\to\mathbb R$ have continuous first partial derivatives on $E^n$. Let $\bar x$ be a solution of (1.1), i.e. $\bar x$ is feasible and $\theta(\bar x)$ is the minimum of $\theta$ on the feasible set $S$. Then there exist $\bar u=(\bar u_0,\bar u_1,\dots,\bar u_m)\in E^{m+1}$ and $\bar v=(\bar v_1,\dots,\bar v_k)\in E^k$ such that
--
--   $$
--   \bar u_0\nabla\theta(\bar x)+\sum_{i=1}^m\bar u_i\nabla g_i(\bar x)+\sum_{j=1}^k\bar v_j\nabla h_j(\bar x)=0, \tag{2.9}
--   $$
--
--   $$
--   \sum_{i=1}^m\bar u_i g_i(\bar x)=0, \tag{2.10}
--   $$
--
--   $$
--   \bar u\ge0, \tag{2.11}
--   $$
--
--   $$
--   (\bar u,\bar v)\ne0. \tag{2.12}
--   $$
--
--   This is the main result of the paper: Fritz John's necessary conditions extended to problems with equality constraints, in a form that does not become trivial when the equalities are present (splitting each equality into two inequalities makes the original conditions hold at every feasible point). It is the basis of the Mangasarian–Fromovitz constraint qualification of §3.
--
--   **Formalization Note** $E^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla$ is Mathlib's `gradient`, and "continuous first partial derivatives on $E^n$" (the standing assumption of §1) is `ContDiff ℝ 1`, equivalent in finite dimension. Indices are `Fin m`, `Fin k` (0-based). $\bar u$ is split into `u0` (multiplier of $\theta$) and `u`; (2.11) is $0\le\bar u_0$ and $0\le\bar u_i$ for all $i$; (2.12) is "$\bar u_0\ne0$ or some $\bar u_i\ne0$ or some $\bar v_j\ne0$". A solution of (1.1) is a global minimizer over $S$ (definition `IsSolution`). $m=0$ and $k=0$ are allowed.
-- source:
--   Mangasarian and Fromovitz, The Fritz John necessary optimality conditions in the presence of equality and inequality constraints, J. Math. Anal. Appl. 17 (1967), p. 41, The generalized Fritz John Necessary Conditions, (2.9)–(2.12)

import Mathlib
import Definitions.Def_MangasarianFJ_GenFJ_Setting

namespace MangasarianFJ.GenFJ
theorem generalized_fritz_john {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hg : ∀ i, ContDiff ℝ 1 (g i)) (hh : ∀ j, ContDiff ℝ 1 (h j))
    (xbar : EuclideanSpace ℝ (Fin n)) (hsol : IsSolution θ g h xbar) :
    ∃ (u0 : ℝ) (u : Fin m → ℝ) (v : Fin k → ℝ),
      u0 • gradient θ xbar + ∑ i, u i • gradient (g i) xbar
          + ∑ j, v j • gradient (h j) xbar = 0 ∧
      ∑ i, u i * g i xbar = 0 ∧
      0 ≤ u0 ∧ (∀ i, 0 ≤ u i) ∧
      (u0 ≠ 0 ∨ (∃ i, u i ≠ 0) ∨ ∃ j, v j ≠ 0) := by sorry
end MangasarianFJ.GenFJ
