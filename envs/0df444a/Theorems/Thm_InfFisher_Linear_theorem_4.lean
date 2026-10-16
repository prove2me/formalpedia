-- Prove2me | Theorems.Thm_InfFisher_Linear_theorem_4
-- name    : InfFisher.Linear.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:53.954989+00:00
-- url     : https://prove2.me/theorems/341c38df-f31a-4277-81e9-210e66b0ace0
-- title:
--   Theorem 4, pp. 15–16 — conic characterization of feasible utilities
-- statement:
--   Let $n\ge2$ and let $v_i(\theta)=c_i\theta+d_i$ be normalized linear valuations on $[0,1]$, with $c_i/2+d_i=1$ and $2\ge d_1\ge\cdots\ge d_n\ge0$. A utility vector belongs to the feasible utility set exactly when it is nonnegative and there exist real $z_i,w_i,s_i,t_i$ satisfying all the linear bounds and parabolic constraints of Theorem 4:
--
--   $$u\in U(v,[0,1])\quad\Longleftrightarrow\quad u\ge0\  \text{and}\  \exists z,w,s,t:\ G_i(s_i,t_i)=(z_i,w_i),\ s_i^2\le t_i,\ 	ext{with the stated utility and box inequalities}.$$
--
--   The complete auxiliary system includes $u_1\le z_1$, $u_i\le z_i+w_{i-1}$ for interior buyers, $u_n\le1+w_{n-1}$, $z_i\in[0,1]$, $w_i\in[-1,0]$, and $z_i+w_i\ge0$. This is a finite convex representation of every feasible utility vector, including vectors below the Pareto frontier.
--
--   **Formalization Note** The printed indices require $n\ge2$. Adjacent intercepts may tie. The paper's further bound on $s_i,t_i$ is a separate companion statement because it fails at a tie.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Theorem 4, pp. 15–16

import Mathlib
import Definitions.Def_InfFisher_Linear_Setting

namespace InfFisher.Linear

open MeasureTheory

/-- Gao–Kroer, Theorem 4, pp. 15–16: the conic characterization of `U(v,[0,1])`. -/
theorem theorem_4 {n : ℕ} (hn : 2 ≤ n) (c d : ℕ → ℝ)
    (hnorm : ∀ i < n, c i / 2 + d i = 1)
    (hd : ∀ i j, i ≤ j → j < n → d j ≤ d i)
    (hd2 : d 0 ≤ 2) (hd0 : 0 ≤ d (n - 1)) :
    ∀ u : Fin n → ℝ,
      u ∈ feasUtil (volume.restrict (Set.Icc (0 : ℝ) 1)) (linVal c d n) ↔
        conicRep n c d u := by sorry

end InfFisher.Linear
