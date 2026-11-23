-- Prove2me | Theorems.Thm_GRH_moebius_square_block_partial_sum_mean
-- name    : GRH.moebius_square_block_partial_sum_mean
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T10:16:34.463922+00:00
-- url     : https://prove2.me/theorems/368312da-d40e-4401-8f0f-61d9319f0153
-- title:
--   Square-block averages of Möbius progression sums
-- statement:
--   Fix a modulus $q\ge 1$, a unit residue $a\pmod q$, and an exponent $1/2<\sigma\le 0.8749570698$. Write $M(n)$ for the partial sum of $\mu$ over the integers $k\le n$ lying in the class $a$. On each complete square interval the claim is
--   $$\left|2M(u)-\frac{1}{2u+1}\sum_{j=0}^{2u} M(u^2+j)\right|\le C(q,a,\sigma)\,(u^2+1)^\sigma.$$
--   The cutoff $\lfloor\sqrt{u^2+j}\rfloor$ is constantly $u$ for $0\le j\le 2u$, so this is the partial-sum contribution to the signed block mean of the centered Möbius bilinear form. No finite Dirichlet series is summed here; the harmonic square is separated from this estimate.
-- source:
--   Helfgott–Thompson, Res. Number Theory 9:6 (2023), arXiv:2101.08773, square-block means of the centered progression bilinear form; the exponent cap is the platform boundary 0.8749570698

import Mathlib
import Definitions.Def_GRH_MoebiusBilinear
open Finset
set_option autoImplicit false

theorem GRH.moebius_square_block_partial_sum_mean
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (σ : ℝ) (hhalf : (1 / 2 : ℝ) < σ) (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
      |2 * (∑ k ∈ Finset.range (u + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) -
        (∑ j ∈ Finset.range (2 * u + 1),
          ∑ k ∈ Finset.range (u ^ 2 + j + 1),
            if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) /
          ((2 * u + 1 : ℕ) : ℝ)| ≤
        C * ((u : ℝ) ^ 2 + 1) ^ σ := by sorry
