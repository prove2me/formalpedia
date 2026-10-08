-- Prove2me | Theorems.Thm_NonsmoothQN_ExactNorm_sin_angle_tendsto_half
-- name    : NonsmoothQN.ExactNorm.sin_angle_tendsto_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:14.642979+00:00
-- url     : https://prove2.me/theorems/bcbfb5e0-ebc5-4001-92c0-3ae86053278b
-- title:
--   §3.1, proof of Theorem 3.2, p. 142 — s ↦ √((1−s)/2) maps [0,1] onto [0,1/√2], contracts there, iterates → 1/2
-- statement:
--   Let $g(s) = \sqrt{(1-s)/2}$ and $I = [0, 1/\sqrt 2]$. Then
--
--   1. $g$ maps $[0,1]$ onto $I$: $g([0,1]) = I$;
--   2. $g$ is a contraction on $I$: there is a constant $K<1$ with $|g(s)-g(s')| \le K|s-s'|$ for all $s,s' \in I$;
--   3. for every sequence with $s_0 \in [0,1]$ and $s_{k+1} = g(s_k)$,
--   $$\lim_{k\to\infty} s_k = \tfrac12 ,$$
--   the fixed point of $g$.
--
--   Applied to $s_k = \sin\theta_k$, this gives $\sin\theta_k \to 1/2$ in the proof of Theorem 3.2.
--
--   **Formalization Note.** The page continues "so the angle $\theta_k$ approaches $\pi/3$". That is a slip: $\sin\theta_k\to 1/2$ with $\theta_k\in(0,\pi/2)$ gives $\theta_k\to\pi/6$; what tends to $\pi/3$ is the turn $\pi/2-\theta_k$, as Theorem 3.2 states. This item does not state the limit of $\theta_k$. The contraction constant is not named on the page; the statement only asserts that one below $1$ exists (the derivative bound on $I$ is about $0.653$).
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 142, §3.1, proof of Theorem 3.2, paragraph after the display for sin θ_{k+1}

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

open Matrix Filter Topology

namespace NonsmoothQN.ExactNorm

theorem sin_angle_tendsto_half :
    angleMap '' Set.Icc (0 : ℝ) 1 = Set.Icc 0 (1 / Real.sqrt 2) ∧
      (∃ K : NNReal, K < 1 ∧ LipschitzOnWith K angleMap (Set.Icc 0 (1 / Real.sqrt 2))) ∧
      ∀ s : ℕ → ℝ, s 0 ∈ Set.Icc (0 : ℝ) 1 → (∀ k, s (k + 1) = angleMap (s k)) →
        Tendsto s atTop (𝓝 (1 / 2)) := by sorry

end NonsmoothQN.ExactNorm
