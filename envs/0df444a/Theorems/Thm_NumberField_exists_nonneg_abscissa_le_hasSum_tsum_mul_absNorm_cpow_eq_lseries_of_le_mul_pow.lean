-- Prove2me | Theorems.Thm_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
-- name    : NumberField.exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/b36f4082-58d0-50c1-9590-2b9e664daf65
-- title:
--   Sums over finite places as a Dirichlet series, abscissa ≤ 2
-- statement:
--   Let $K$ be a number field, and for each $v$ in the height-one spectrum of the ring of integers $\mathcal{O}_K$ (i.e. each nonzero prime ideal, written $v$ with underlying ideal `v.asIdeal` of absolute norm $N(v)$) let $m \mapsto c_{v,m}$ be a real sequence. Assume $c_{v,0} = 0$ for every $v$, that $0 \le c_{v,m}$ for all $v$ and all $m$, and that there is a single real constant $B$ with $c_{v,m} \le B \cdot N(v)^m$ for all $v$ and all $m$. The assertion is that there exists a sequence $d \colon \mathbb{N} \to \mathbb{R}$ such that: $d_n \ge 0$ for every $n$; the abscissa of absolute convergence of the $L$-series of $n \mapsto (d_n : \mathbb{C})$ is at most $2$ (as an element of $\overline{\mathbb{R}}$); and for every $s \in \mathbb{C}$ with $\operatorname{Re} s > 2$, first, for each $v$ the series $\sum_m c_{v,m}\,(N(v)^{-s})^m$ is summable, and second, the family indexed by the finite places, whose value at $v$ is the sum $\sum_m' c_{v,m}\,(N(v)^{-s})^m$, is summable with total sum $\sum_n' d_n n^{-s}$, the $L$-series of $d$ at $s$.
--
--   This repackages a double sum over the finite places of $K$ and over powers as an ordinary Dirichlet series with non-negative coefficients, convergent in the half-plane $\operatorname{Re} s > 2$; the bound $c_{v,m} \le B\,N(v)^m$ together with the fact that only finitely many pairs $(v,m)$ have $N(v)^m$ equal to a given integer gives the coefficient growth needed for the abscissa bound, and summability over places uses [`NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt`](thm.html#NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt). It serves the non-vanishing argument [`AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat`](thm.html#AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat), where a logarithm of an Euler product must be compared with a Dirichlet series having non-negative coefficients so that a Landau-type theorem applies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow.lean

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
    (K : Type) [Field K] [NumberField K]
    (c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ)
    (hc0 : ∀ v : HeightOneSpectrum (𝓞 K), c v 0 = 0)
    (hc : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), 0 ≤ c v m)
    (B : ℝ) (hcB : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ),
      c v m ≤ B * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      ∀ s : ℂ, 2 < s.re →
        (∀ v : HeightOneSpectrum (𝓞 K),
          Summable (fun m : ℕ => (c v m : ℂ) * ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) ^ m)) ∧
        HasSum (fun v : HeightOneSpectrum (𝓞 K) =>
            ∑' m : ℕ, (c v m : ℂ) * ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s) := by sorry
