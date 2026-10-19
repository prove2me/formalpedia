-- Prove2me | Theorems.Thm_GreenTao_progression_cs_cube_bound
-- name    : GreenTao.progression_cs_cube_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:19:18.561204+00:00
-- url     : https://prove2.me/theorems/09c2763c-45ae-419c-a9ef-c97fb37c8bad
-- title:
--   Finite progression-to-weighted-cube Cauchy–Schwarz bound
-- statement:
--   Let $d\ge2$, let $m>d$ be prime, and let $\mu:\mathbb Z/m\mathbb Z\to[0,\infty)$. Let $F_0,\ldots,F_d$ be real functions dominated in absolute value by $\mu$, and distinguish a position $j$. With the progression Cauchy–Schwarz factor $P$ and cube weight $W$ defined from the translated consecutive coefficients,
--
--   $$|T_{d+1}(F_0,\ldots,F_d)|^{2^d}\le P\,C_d^W(F_j).$$
--
--   Here $P=\prod_{l=0}^{d-1}P_l^{2^{d-1-l}}$ is the product of the stage factors from equation (5.18), and $W$ is the explicit progression-difference version of the weight in equation (5.25). This is the finite Cauchy–Schwarz part of the generalized von Neumann argument; it does not assume pseudorandomness or any asymptotic moment estimate.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 Lemma 5.4, equations (5.19)–(5.25), including the uniform-cover reparameterization and the paired expression for W. The project’s csWeight averages directly over the progression difference, replacing redundant fiber coordinates.

import Definitions.Def_GreenTao_ProgressionCS
open scoped BigOperators

theorem GreenTao.progression_cs_cube_bound
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ+) (hm : Nat.Prime (m : ℕ)) (hdm : d < (m : ℕ))
    (μ : ZMod (m : ℕ) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (j : Fin (d + 1)) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (hF : ∀ i x, |F i x| ≤ μ x) :
    |GreenTao.mixedAPAvg (d + 1) F| ^ (2 ^ d) ≤
      GreenTao.csFactor d j μ *
        GreenTao.weightedCubeAvg d (GreenTao.csWeight d j μ) (F j) := by sorry
