-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_picard_convergence
-- name    : HarrisonReimanRBM.Orthant.picard_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:22:10.506985+00:00
-- url     : https://prove2.me/theorems/261208c0-64bf-4618-8e13-1598fa6e1beb
-- title:
--   Picard iteration (16)–(19): $y^n\to y$ uniformly on compacts, $y$ the unique solution of (13)–(14)
-- statement:
--   Let $K\ge1$ and let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and maximal column sum $\max_j\sum_i q_{ij}<1$. Fix $x\in C_S$ and let $\pi(y)(t)=\sup_{0\le s\le t}[y(s)Q-x(s)]^+$. Define
--   $$y^0(t)\equiv0,\qquad y^{n+1}=\pi(y^n),\quad n=0,1,2,\dots\qquad(16)\text{–}(18).$$
--   Then there is a path $y$ such that
--
--   1. $y\in C_0$ (continuous, nondecreasing, $y(0)=0$) and $y(t)=\pi(y)(t)$ for all $t\ge0$;
--   2. every $y'\in C_0$ with $y'(t)=\pi(y')(t)$ for all $t\ge0$ coincides with $y$ on $[0,\infty)$;
--   3. $y^n\to y$ uniformly on compact intervals of $[0,\infty)$ (19).
--
--   This gives existence and uniqueness for the fixed-point formulation (13)–(14), together with the explicit construction (16)–(18).
--
--   **Formalization Note** The paper works under $\|Q\|=\alpha<1$, printed as the maximal row sum; as in the contraction milestone, the norm that makes $\pi$ a contraction under the row-vector convention is the maximal column sum, which is assumed here. Uniform convergence on compacts is `Reiman84.QueueLength.UocTendsto`.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), pp. 304–305, proof of Theorem 1, (16)–(19)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace HarrisonReimanRBM.Orthant

open Reiman84.QueueLength

/-- Proof of Theorem 1, pp. 304–305, (16)–(19): if `Q ≥ 0` has zero diagonal and maximal
column sum `< 1`, then for `x ∈ C_S` the system (13)–(14) (`y ∈ C₀`, `y = π(y)` on
`[0, ∞)`) has a unique solution `y`, and the Picard iterates `y⁰ ≡ 0`, `yⁿ⁺¹ = π(yⁿ)`
converge to `y` uniformly on compact intervals. -/
theorem picard_convergence {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (hQd : ∀ j, Q j j = 0) (hcol : maxColSum Q < 1)
    (x : ℝ → Fin K → ℝ) (hx : IsCPlus x) :
    ∃ y : ℝ → Fin K → ℝ, InC0 y ∧ (∀ t, 0 ≤ t → y t = piMap Q x y t) ∧
      (∀ y' : ℝ → Fin K → ℝ, InC0 y' → (∀ t, 0 ≤ t → y' t = piMap Q x y' t) →
        ∀ t, 0 ≤ t → y' t = y t) ∧
      UocTendsto (fun n => picardIter Q x n) y := by sorry

end HarrisonReimanRBM.Orthant
