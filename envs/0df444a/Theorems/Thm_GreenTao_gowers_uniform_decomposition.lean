-- Prove2me | Theorems.Thm_GreenTao_gowers_uniform_decomposition
-- name    : GreenTao.gowers_uniform_decomposition
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-16T20:54:04.589787+00:00
-- url     : https://prove2.me/theorems/9ec91175-85ce-4c06-838f-cecc70ced404
-- title:
--   Gowers-uniform structured decomposition for a pseudorandom majorant
-- statement:
--   Let $k\ge3$, let $M_n$ be prime moduli tending to infinity, and let $\nu_n$ be a $k$-pseudorandom family in the project's existing sense. Suppose $0\le f_n\le\nu_n$. For every pair of tolerances $\varepsilon,\rho>0$, all sufficiently large $n$ admit real functions $s,u$ on $G_n=\mathbb Z/M_n\mathbb Z$ such that
--
--   $$0\le s\le1+\varepsilon,\qquad 0\le s+u\le f_n,$$
--
--   $$\mathbb E s\ge\mathbb E f_n-\varepsilon,\qquad |C_{k-1}(u)|\le\rho.$$
--
--   Here $C_d$ is the real Gowers cube average, the $2^d$-th power of the $U^d$ norm for $d\ge1$. The structured part is nearly bounded by one, the uniform part has arbitrarily small Gowers uniformity, and their sum may discard a nonnegative exceptional contribution. The mean tolerance and uniformity tolerance are independent.
--
--   This is the functional consequence of the generalized Koopman–von Neumann structure theorem used in the application immediately following Proposition 8.1. It supplies the structure input to the existing bounded-model leaf.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §8 Proposition 8.1, equations (8.1)–(8.3), and the definitions and mean/boundedness estimates for f_U and f_{U^⊥} at the start of the proof of Theorem 3.5 assuming Proposition 8.1. This is an epsilon/rho consequence for the two resulting functions, not the full sigma-algebra/exceptional-set statement.

import Definitions.Def_GreenTao_Uniformity
open Filter

theorem GreenTao.gowers_uniform_decomposition
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν f : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x)
    (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∀ᶠ n in atTop, ∃ s u : ZMod (M n : ℕ) → ℝ,
      (∀ x, 0 ≤ s x ∧ s x ≤ 1 + ε) ∧
      (∀ x, 0 ≤ s x + u x ∧ s x + u x ≤ f n x) ∧
      GreenTao.avg (f n) - ε ≤ GreenTao.avg s ∧
      |GreenTao.cubeAvg (k - 1) u| ≤ ρ := by sorry
