-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
-- name    : LanglandsTunnell.RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/21c0dd98-9185-5d31-a3fc-c5302d58667b
-- title:
--   Third induced Euler coefficient at an unramified prime of a cubic field
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}] = \operatorname{finrank}_{\mathbb{Q}} K = 3$, let $c$ be an arbitrary complex-valued function on the height-one primes of $\mathcal{O}_K$, and let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$. Write $\mathrm{primeFibre}\ \mathbb{Q}\ K\ v$ for the set of height-one primes $\mathfrak{P}$ of $\mathcal{O}_K$ with $\mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}} = v$ (that is, $\mathfrak{P}.\mathrm{under}\,\mathcal{O}_{\mathbb{Q}} = v$). Assume $v$ is not ramified in $K$ in the sense of the predicate `IsRamifiedIn`: there is no $\mathfrak{P}$ in this fibre with $\mathrm{ramificationIdx}'(v,\mathfrak{P}) \neq 1$, i.e. every prime of $K$ above $v$ has ramification index $1$. Then the quantity $\mathrm{inducedE3}\ \mathbb{Q}\ c\ v$, defined as minus the coefficient of $X^{3}$ in the induced Euler polynomial $\prod^{\mathrm{f}}_{\mathfrak{P} \mid v} \mathrm{inducedFactor}\ \mathbb{Q}\ c\ \mathfrak{P}$ (a finitely-supported product over the fibre), equals
--   $$(-1)^{\,\#\{\mathfrak{P} \mid v\}+1}\ \prod_{\mathfrak{P} \mid v} c(\mathfrak{P}),$$
--   the cardinality being `Nat.card` of the fibre and the product again a finitely-supported product over it.
--
--   This is the unramified Euler-factor computation for the cubic induction: at a prime $v$ unramified in a cubic field $K$, the third coefficient of the induced local Euler polynomial collapses to a sign times the product of the coefficients $c(\mathfrak{P})$ over the primes above $v$. It feeds the conductor estimates for the induced automorphic datum, being cited by the results bounding conductor exponents for data whose Euler coefficients are given by `inducedE3`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    inducedE3 ℚ c v = (-1) ^ (Nat.card (primeFibre ℚ K v) + 1) * ∏ᶠ w ∈ primeFibre ℚ K v, c w := by sorry
