-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd
-- name    : LanglandsTunnell.RankinSelberg.hasProd_inv_eval_inducedEulerPoly_of_hasProd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e83bd702-4eaa-5e1b-808c-bab225e84096
-- title:
--   Regrouping an Euler product over K along the primes of F
-- statement:
--   Let $F$ and $K$ be number fields, with the ring of integers $\mathcal{O}_K$ carrying the structure of an $\mathcal{O}_F$-algebra that is integral over $\mathcal{O}_F$. Let $c$ be a complex-valued function on the height-one spectrum of $\mathcal{O}_K$, i.e. on the non-zero prime ideals $\mathfrak{P}$ of $\mathcal{O}_K$, and let $s, Z \in \mathbb{C}$. Assume that the family $\bigl(1 - c(\mathfrak{P}) \, N(\mathfrak{P})^{-s}\bigr)^{-1}$, indexed by the non-zero primes $\mathfrak{P}$ of $\mathcal{O}_K$, has unconditional product $Z$ in the sense of `HasProd`, where $N$ denotes the absolute norm `Ideal.absNorm` of an ideal, cast to $\mathbb{C}$, and the exponentiation is the complex power. Then the family indexed by the non-zero primes $p$ of $\mathcal{O}_F$ whose term at $p$ is the inverse of the value at $N(p)^{-s}$ of the polynomial `inducedEulerPoly F c p` also has unconditional product $Z$. Here `inducedEulerPoly F c p` is the finite product (a `finprod` over a set), taken over those $\mathfrak{P}$ with $\mathfrak{P} \cap \mathcal{O}_F = p$, of the polynomials $1 - c(\mathfrak{P}) X^{f}$, the exponent $f$ being `Ideal.inertiaDeg'` of $p$ at $\mathfrak{P}$.
--
--   This is the classical passage from an Euler product over the primes of $K$ to an Euler product over the primes of $F$ whose local factor at $p$ is the induced (automorphically induced) Euler polynomial attached to the fibre above $p$. It is used in the Langlands–Tunnell part of the argument, where the induced Euler factors and their analytic properties are studied: it is cited in the treatment of the twisted Euler products attached to the cubic induction situation, both for the existence of entire twists and for non-vanishing of the regrouped factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.RankinSelberg.hasProd_inv_eval_inducedEulerPoly_of_hasProd
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] (c : HeightOneSpectrum (𝓞 K) → ℂ) (s Z : ℂ)
    (h : HasProd (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) Z) :
    HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) Z := by sorry
