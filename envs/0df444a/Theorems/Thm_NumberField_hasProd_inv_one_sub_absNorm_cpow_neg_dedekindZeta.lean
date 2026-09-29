-- Prove2me | Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
-- name    : NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4d2ff9db-ed2c-5abd-b0b8-310b6480163c
-- title:
--   Euler product for the Dedekind zeta function
-- statement:
--   Let $K$ be a number field, i.e. a field $K$ (in the type universe of `Type`) equipped with the structure making it a finite extension of $\mathbb{Q}$, and let $s$ be a complex number with $\operatorname{Re} s > 1$. The assertion is that the family indexed by the height-one spectrum of the ring of integers $\mathcal{O}_K$ — that is, by the nonzero prime ideals $v$ of $\mathcal{O}_K$ — whose $v$-th member is $\bigl(1 - (\mathrm{N}v)^{-s}\bigr)^{-1}$, where $\mathrm{N}v =$ `Ideal.absNorm` of the ideal underlying $v$, a natural number cast into $\mathbb{C}$, and the complex power is the principal one, has unconditional product equal to `NumberField.dedekindZeta K s`, the Dedekind zeta function of $K$ at $s$ (Mathlib's $L$-series whose $n$-th coefficient counts the integral ideals of $\mathcal{O}_K$ of absolute norm $n$). `HasProd` is the unconditional notion: the net of finite partial products, indexed by the finite sets of primes ordered by inclusion, converges to $\zeta_K(s)$; in particular the product converges and no ordering of the primes is chosen.
--
--   This is the classical Euler product expansion of the Dedekind zeta function in the half-plane $\operatorname{Re} s > 1$, in the unconditional-convergence form. It is the source of every partial Euler product over finite places used later: splitting off a finite set of primes and comparing with the full product is how the incomplete zeta and $L$-functions occurring in the analytic arguments are related to $\zeta_K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by sorry
