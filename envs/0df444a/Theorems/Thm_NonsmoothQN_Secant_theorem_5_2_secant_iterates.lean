-- Prove2me | Theorems.Thm_NonsmoothQN_Secant_theorem_5_2_secant_iterates
-- name    : NonsmoothQN.Secant.theorem_5_2_secant_iterates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:32.711082+00:00
-- url     : https://prove2.me/theorems/0e8949f6-e644-4975-bbd0-e718249a108d
-- title:
--   Theorem 5.2, pp. 152–153 — the secant method on $|x|$ follows the alternating binary expansion of $x_0$
-- statement:
--   Let $x_0>0$ and let
--   $$x_0=\sum_{j=0}^{m}(-1)^j\,2^{-a_j}\qquad(m\in\{0,1,2,\dots\}\cup\{\infty\},\ a_0<a_1<\cdots)$$
--   be its canonical alternating binary expansion (if $1\le m<\infty$ then $a_m\ge a_{m-1}+2$). Apply the secant method to minimize $f(x)=|x|$, using the inexact line search of §5.1 (Algorithm 4.6 with $A(t):t<-2x_k/p_k$ and $W(t):t\ge-x_k/p_k$), starting at $x_0$ with $H_0=1$. Then:
--   1. the iterates are the tails of the expansion,
--   $$x_k=\sum_{j=k}^{m}(-1)^j\,2^{-a_j}\qquad\text{for all integers }0\le k\le m;\qquad(5.3)$$
--   2. the first line search terminates, and calculating $x_1$ takes $1+|a_0|$ trials;
--   3. for every $k$ with $1\le k<m$, the line search from $x_k$ terminates, and calculating $x_{k+1}$ takes $a_k-a_{k-1}$ trials;
--   4. if $m<\infty$, the secant method terminates at zero after finitely many function trials: there is $K$ with $x_K=0$ and each of the line searches before it terminates;
--   5. if $m=\infty$, the sequence of all function trial values $|z_j|$ converges to zero R-linearly with rate $\tfrac12$.
--
--   The secant method on $|x|$ therefore costs essentially the same number of function trials as bisection, in contrast with steepest descent.
--
--   **Formalization Note** The page says "with arbitrary $x_0$"; the expansion exists only for $x_0>0$ and (5.3) forces $x_0>0$, so $x_0>0$ is assumed ($x_0<0$ is the mirror image, $x_0=0$ is excluded by Algorithm 2.1 since $|x|$ is not differentiable there). "For all $k<m$" in the trial count needs $k\ge1$ (for $k=0$ the count is the separate $1+|a_0|$, and $a_{-1}$ is undefined). The expansion is assumed canonical, as the uniqueness claim requires (see the milestone on the first sentence of Theorem 5.2). The function trial values are $|z_j|$ for the trial points $z_j$ of all line searches in order (the starting value $|x_0|$ is not included; including it does not change R-linear convergence). R-linear convergence is the definition of p. 141, not a bound $C2^{-j}$.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 152–153, Theorem 5.2 (secant-method part) and (5.3)

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic
import Definitions.Def_NonsmoothQN_Secant_Expansion

namespace NonsmoothQN.Secant

theorem theorem_5_2_secant_iterates (x₀ : ℝ) (hx₀ : 0 < x₀) (m : ℕ∞) (a : ℕ → ℤ)
    (hexp : IsAltBinExpansion x₀ m a) (hcan : IsCanonicalExpansion m a) :
    (∀ k : ℕ, (k : ℕ∞) ≤ m → secX x₀ 1 k = tailSum m a k) ∧
    (secLSTerminates x₀ 1 0 ∧ (secTrials x₀ 1 0 : ℤ) = 1 + |a 0|) ∧
    (∀ k : ℕ, 1 ≤ k → (k : ℕ∞) < m →
      secLSTerminates x₀ 1 k ∧ (secTrials x₀ 1 k : ℤ) = a k - a (k - 1)) ∧
    (m ≠ ⊤ → ∃ K : ℕ, secX x₀ 1 K = 0 ∧ ∀ k < K, secLSTerminates x₀ 1 k) ∧
    (m = ⊤ → IsRLinear (fun j => |allTrial x₀ 1 j|) 0 (1 / 2)) := by sorry

end NonsmoothQN.Secant
