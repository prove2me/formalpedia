-- Prove2me | Theorems.Thm_ModularCurve_jqModC_mem_adjoin_jqNModC_of_prime_of_ne
-- name    : ModularCurve.jqModC_mem_adjoin_jqNModC_of_prime_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3cc27f19-a19c-5fac-8148-0a874615af46
-- title:
--   j(q) lies in K(j(q^s), j(q^ℓ), j(q^{sℓ}))
-- statement:
--   Let $K$ be a field and let $s, \ell$ be non-zero natural numbers, with $s\ell$ also non-zero, such that $s$ and $\ell$ are prime and $s \neq \ell$, and such that the image of $s\ell$ in $K$ is non-zero. Inside the field of Laurent series $K((q))$ (Hahn series over $K$ with integer exponents) write $\mathtt{jqModC}\,K$ for the element $q^{-1}$ times the power series obtained from the integral series $\mathtt{jNum} = E_4^3 \cdot \eta^{-\text{unit}}$ (the product of the cube of the Eisenstein series of weight $4$ with the inverse of the Dedekind eta unit) by reducing its coefficients along $\mathbb{Z} \to K$; this is the $q$-expansion $j(q) = q^{-1} + 744 + \cdots$ of the modular invariant read in $K$. For a non-zero natural number $N$, $\mathtt{jqNModC}\,K\,N$ is the image of $j(q)$ under the ring homomorphism $\mathtt{qExpand}\,K\,N$ of $K((q))$ that multiplies all exponents by $N$, i.e. the substitution $q \mapsto q^N$, so it is $j(q^N)$. The assertion is that $j(q)$ belongs to the intermediate field of $K((q))$ generated over $K$ by the three elements $j(q^s)$, $j(q^\ell)$ and $j(q^{s\ell})$.
--
--   This is the $q$-expansion form of the classical fact that the function field of $X_0(s\ell)$ is generated over $K$ by the pull-backs of the function fields of $X_0(s)$ and $X_0(\ell)$ along the two degeneracy maps, the generating element $j(q)$ of the level-one field being recovered from the three expansions $j(q^s)$, $j(q^\ell)$, $j(q^{s\ell})$. It serves as the generation input for the commutation of the Hecke correspondences at distinct primes, used in [`ModularCurve.degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd`](thm.html#ModularCurve.degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jqModC_mem_adjoin_jqNModC_of_prime_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.jqModC_mem_adjoin_jqNModC_of_prime_of_ne (K : Type*) [Field K] (s ℓ : ℕ)
    [NeZero s] [NeZero ℓ] [NeZero (s * ℓ)] (hs : s.Prime) (hℓ : ℓ.Prime) (hne : s ≠ ℓ)
    (hK : ((s * ℓ : ℕ) : K) ≠ 0) :
    jqModC K ∈ IntermediateField.adjoin K
      ({jqNModC K s, jqNModC K ℓ, jqNModC K (s * ℓ)} : Set (LaurentSeries K)) := by sorry
