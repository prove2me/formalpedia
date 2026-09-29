-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
-- name    : LanglandsTunnell.TateLocal.exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/44f3fa63-ebb5-5a15-8b9d-3a1395fafea1
-- title:
--   Polar decomposition of a local character of conductor exponent c
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of its ring of integers, and let $\chi : (K_v)^\times \to \mathbb{C}^\times$ be a homomorphism of groups from the units of the $v$-adic completion $K_v$ to $\mathbb{C}^\times$ (no continuity is assumed). Suppose $\chi$ has conductor exponent $c \in \mathbb{N}$ at $v$ in the sense of the predicate `HasConductorExponentAt`: $\chi(u) = 1$ for every unit $u$ with $v$-valuation $\mathrm{Valued.v}(u) = 1$ satisfying, in case $c > 0$, also $\mathrm{Valued.v}(u - 1) \le \exp(-c)$; and for every $m < c$ there is a unit $u$ with valuation $1$ satisfying the corresponding condition at level $m$ (vacuous when $m = 0$) with $\chi(u) \ne 1$. Then there exist a homomorphism $\eta : (K_v)^\times \to \mathbb{C}^\times$ and a real number $\sigma$ such that: $\|\eta(z)\| = 1$ for every $z$, so $\eta$ is unitary; $\eta$ again has conductor exponent exactly $c$ at $v$ in the same sense; and for every $z$ one has $\chi(z) = \eta(z)\,\cdot\,\mathrm{modulus}(z)^{\sigma}$, where $\mathrm{modulus}$ is the module of a nonzero element given by the distributive Haar character (equal to the $v$-adic norm $\|\cdot\|_{v}$ on $K_v$), the power being the complex power of the real number $\mathrm{modulus}(z)$ with exponent $\sigma$ viewed in $\mathbb{C}$.
--
--   This is the polar decomposition of a quasi-character of a non-archimedean local field: a character of conductor exponent $c$ is the product of a unitary character of the same conductor exponent and an unramified real power of the absolute value. It is used in the local theory of zeta integrals of this development, in the normalisation of local Rankin–Selberg integrals and in the construction of admissible gauges for Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c) :
    ∃ (η : (v.adicCompletion K)ˣ →* ℂˣ) (σ : ℝ),
      (∀ z : (v.adicCompletion K)ˣ, ‖((η z : ℂˣ) : ℂ)‖ = 1) ∧
      HasConductorExponentAt K v η c ∧
      ∀ z : (v.adicCompletion K)ˣ, ((χ z : ℂˣ) : ℂ) =
        ((η z : ℂˣ) : ℂ) * ((modulus (z : v.adicCompletion K) : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ) := by sorry
