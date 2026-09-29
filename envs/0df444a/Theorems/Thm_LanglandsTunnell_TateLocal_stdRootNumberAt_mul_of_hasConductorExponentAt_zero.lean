-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
-- name    : LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/869e4524-2d4c-52f5-990e-d4dac02e26e2
-- title:
--   Unramified twist of the standard local root number
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of its ring of integers, with $v$-adic completion $K_v$, and let $\chi,\omega\colon K_v^\times\to\mathbb{C}^\times$ be group homomorphisms. Let $c$ be a natural number and assume $\chi$ has conductor exponent $c$ in the sense that $\chi$ is trivial on $\{u : |u|_v=1$ and ($c=0$ or $|u-1|_v\le \exp(-c))\}$ while for every $m<c$ some unit of that shape with parameter $m$ is not killed by $\chi$; assume likewise that $\omega$ has conductor exponent $0$, i.e. $\omega$ is trivial on the units of valuation $1$ (the second clause being vacuous). Assume further that the complex numbers $\chi(\varpi_v)$ and $\omega(\varpi_v)$ have absolute value $1$, where $\varpi_v$ is the fixed uniformizer unit of $K_v$ coming from a chosen uniformizer of $v$ in $\mathcal{O}_K$, and that the local component $\psi_{K,v}$ at $v$ of the standard additive character of the adele ring of $K$ is non-trivial. Then the standard local root number of the twisted character, i.e. the standard local $\varepsilon$-factor at $s=1/2$ formed with the self-dual Haar measure, $\psi_{K,v}$ and the standard test function, satisfies $$\varepsilon(\chi\omega)=\omega(\varpi_v)^{\,c+n}\,\varepsilon(\chi),$$ where $n$ is the level of $\psi_{K,v}$, the supremum of the integers $m$ with $\psi_{K,v}$ trivial on $\{x : |x|_v\le\exp(m)\}$, and the exponent $c+n$ is taken in $\mathbb{Z}$.
--
--   This is the standard behaviour of Tate's local root number under twisting by an unramified character of absolute value $1$ on the uniformizer, in the normalisation attached to the standard additive character and its self-dual measure. It is used throughout the local bookkeeping of the converse-theorem step, for instance in the computations of products of twisted root numbers and in the cusp-synthesis arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c)
    (hω : HasConductorExponentAt K v ω 0) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1)
    (huω : ‖(ω (uniformizerUnit K v) : ℂ)‖ = 1) (hψ : psiLocal K v ≠ 1) :
    stdRootNumberAt K v (χ * ω)
      = (ω (uniformizerUnit K v) : ℂ) ^ ((c : ℤ) + addCharLevel (psiLocal K v))
          * stdRootNumberAt K v χ := by sorry
