-- Prove2me | Theorems.Thm_KeatingSnaith_selberg_morris_one
-- name    : KeatingSnaith.selberg_morris_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T12:13:12.437683+00:00
-- url     : https://prove2.me/theorems/4608b98f-ca2c-4396-880a-6620e56aa96e
-- title:
--   Selberg's integral, the $\gamma = 1$ case
-- statement:
--   This is the variant of **Selberg's integral** used throughout Chapter 2 of the source, in the case $a=b=1$, $\gamma=1$ that the chapter actually needs.
--
--   Let $N\ge 1$ and let $\alpha,\beta$ be real numbers subject to
--
--   1. $\alpha > N-1$,
--   2. $\beta > N-1$,
--   3. $\alpha+\beta-1 > 2(N-1)$.
--
--   These are the conditions (2.1.3) of the source at $\gamma=1$; the third is exactly what makes the integral converge. Then
--
--   $$
--   \int_{\mathbb{R}^N} \prod_{1\le j<k\le N}(x_j-x_k)^2 \prod_{n=1}^{N}(1+ix_n)^{-\alpha}(1-ix_n)^{-\beta}\,dx
--   = \frac{(2\pi)^N}{2^{(\alpha+\beta)N-N(N-1)-N}}\prod_{j=0}^{N-1}\frac{\Gamma(2+j)\,\Gamma(\alpha+\beta-N-j)}{\Gamma(2)\,\Gamma(\alpha-j)\,\Gamma(\beta-j)} ,
--   $$
--
--   where the complex powers are taken with the principal branch (legitimate since $1\pm ix_n$ has real part $1>0$).
--
--   This evaluation is the analytic engine of the whole chapter: each CUE average computed in the mission is brought into this shape by a change of variables and then read off from the right-hand side. It is of independent interest as the first Selberg-type integral available in a formal library.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 30, eq. (2.1.2) with the validity conditions (2.1.3), specialised to gamma = 1 and a = b = 1

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- Selberg–Morris integral, the `γ = 1` case (thesis eq. (2.1.2)–(2.1.3)). -/
theorem selberg_morris_one (N : ℕ) (hN : 1 ≤ N) (a b : ℝ)
    (ha : (N : ℝ) - 1 < a) (hb : (N : ℝ) - 1 < b)
    (hab : 2 * ((N : ℝ) - 1) < a + b - 1) :
    ∫ x : Fin N → ℝ,
        ((∏ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
            (x p.1 - x p.2) ^ 2 : ℝ) : ℂ) *
          ∏ n, ((1 + x n * Complex.I) ^ (-a : ℂ) * (1 - x n * Complex.I) ^ (-b : ℂ))
      = (((2 * Real.pi) ^ N / (2 : ℝ) ^ ((a + b) * N - N * ((N : ℝ) - 1) - N) *
            ∏ j ∈ Finset.range N,
              Real.Gamma (2 + j) * Real.Gamma (a + b - N - j) /
                (Real.Gamma 2 * Real.Gamma (a - j) * Real.Gamma (b - j)) : ℝ) : ℂ) := by
  sorry

end KeatingSnaith
