-- Prove2me | Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd
-- name    : NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/b930d29e-1ff6-5adf-8c1f-d13a9059241f
-- title:
--   Euler product for a restricted Dedekind zeta function
-- statement:
--   Let $K$ be a number field (a field with a `NumberField` instance), let $p$ be an arbitrary predicate on the height one spectrum of the ring of integers $\mathcal{O}_K$, i.e. on the set of non-zero prime ideals of $\mathcal{O}_K$, and let $s \in \mathbb{C}$ satisfy $\operatorname{Re} s > 1$. Define the arithmetic function $a(n)$, for $n \in \mathbb{N}$, to be the cardinality (`Nat.card`, cast into $\mathbb{C}$) of the set of ideals $I \subseteq \mathcal{O}_K$ whose absolute norm `Ideal.absNorm I` equals $n$ and all of whose prime divisors $v$ (i.e. those $v$ in the height one spectrum with $v.\mathrm{asIdeal} \mid I$) satisfy $p\,v$. The theorem asserts two things simultaneously. First, the Dirichlet series $\sum_{n \ge 1} a(n) n^{-s}$ is absolutely summable at $s$ in the sense of `LSeriesSummable`. Second, the family indexed by the subtype $\{v \mid p\,v\}$ of primes satisfying $p$, with $v$-th term $\bigl(1 - N(v.\mathrm{asIdeal})^{-s}\bigr)^{-1}$ where $N$ denotes the absolute norm, is unconditionally multipliable with product (in the sense of `HasProd`, i.e. the net of finite partial products converges) equal to the value $\mathrm{LSeries}\,a\,s$ of that Dirichlet series at $s$.
--
--   This is the Euler product expansion of a restricted (partial) Dedekind zeta function: the product of the local factors over an arbitrary set $P$ of primes of $\mathcal{O}_K$ equals the Dirichlet series counting, by norm, the ideals all of whose prime divisors lie in $P$; taking $p$ identically true gives the Euler product of $\zeta_K$, and taking $P$ the complement of a finite set gives the partial zeta functions $\zeta_{K,T}$. It is used in the global analytic input to Tate's theory, by [`NumberField.TateGlobal.apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one`](thm.html#NumberField.TateGlobal.apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd
    (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K) → Prop) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 K) //
        Ideal.absNorm I = n ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → p v} : ℂ)) s ∧
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // p v} =>
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => (Nat.card {I : Ideal (𝓞 K) //
        Ideal.absNorm I = n ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → p v} : ℂ)) s) := by sorry
