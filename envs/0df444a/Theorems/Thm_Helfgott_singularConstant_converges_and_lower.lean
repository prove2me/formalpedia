-- Prove2me | Theorems.Thm_Helfgott_singularConstant_converges_and_lower
-- name    : Helfgott.singularConstant_converges_and_lower
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T01:52:37.138315+00:00
-- url     : https://prove2.me/theorems/812041de-2b2b-46ff-aa59-1e80b5076b7f
-- title:
--   Convergence and uniform lower bound for the actual ternary singular-series Euler product
-- statement:
--   For every odd nonnegative integer $N$, the ternary singular-series Euler product
--
--   $$C_0(N)=\prod_{p\mid N}\left(1-\frac1{(p-1)^2}\right)
--   \prod_{p\nmid N}\left(1+\frac1{(p-1)^3}\right)$$
--
--   converges, and
--
--   $$C_0(N)\ge\frac{33}{25}=1.32.$$
--
--   Both products run over primes. The factor at two equals two because $N$ is odd. This is a uniform arithmetic lower bound for the actual main-term Euler factor in Helfgott's ternary Goldbach construction. It does not assert a major-arc approximation or an identity with an infinite Ramanujan series. The rational constant is coarser than the sharper bound in the cited paper.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §7.2, equations (7.9)–(7.10). The explicit lower bound 1.32 is independently derived from kernel-checked finite Euler certificates and a proved complete tail estimate; convergence follows from a summable norm-defect bound. Written by Codex.

import Definitions.Def_Helfgott_SingularSeries

theorem Helfgott.singularConstant_converges_and_lower (N : ℕ) (hodd : Odd N) :
    HasProd (Helfgott.singularEulerFactor N) (Helfgott.singularConstant N) ∧
    (33/25:ℝ) ≤ Helfgott.singularConstant N := by sorry
