-- Prove2me | Theorems.Thm_Ideal_snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal
-- name    : Ideal.snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/30a7c707-4333-5bef-9e98-6679dabf70cc
-- title:
--   No tangent directions at an isolated reduced point
-- statement:
--   Let $L$ be a field of characteristic zero, let $R$ be a commutative $L$-algebra which is reduced, and let $\mathfrak p \subseteq R$ be an ideal which is a minimal prime over the zero ideal (i.e. $\mathfrak p \in (\bot : \mathrm{Ideal}\,R).\mathrm{minimalPrimes}$), which is moreover maximal, and such that the quotient $R/\mathfrak p$ is a finite $L$-module. Let $K$ be a field equipped with an $L$-algebra structure, and let $\varphi : R \to K[\varepsilon]/(\varepsilon^2)$ be an $L$-algebra homomorphism into the dual numbers over $K$, subject to the condition that the kernel of the ring homomorphism obtained by composing $\varphi$ with the projection $\mathrm{fst} : K[\varepsilon]/(\varepsilon^2) \to K$ is exactly $\mathfrak p$. The conclusion is that for every $r \in R$ the $\varepsilon$-component of $\varphi(r)$ vanishes, i.e. $\varphi(r) = \mathrm{fst}(\varphi(r))$ lies in the image of the scalars $K \hookrightarrow K[\varepsilon]/(\varepsilon^2)$; equivalently, $\varphi$ carries no infinitesimal information beyond its reduction modulo $\varepsilon$.
--
--   This is the statement that a point cut out by a minimal-and-maximal prime of a reduced algebra in characteristic zero, with finite residue algebra, is an isolated point carrying no nonzero tangent vector: every $L$-algebra map to the dual numbers with that prime as the kernel of its reduction is constant in the $\varepsilon$-direction. It is used in the study of minimal primes of tensor products attached to modular curves, in [`ModularCurve.FullLevel.not_isMaximal_of_mem_minimalPrimes_tensorProduct_gamma0Pow`](thm.html#ModularCurve.FullLevel.not_isMaximal_of_mem_minimalPrimes_tensorProduct_gamma0Pow) and in [`ModularCurve.FullLevel.Diamond.not_isMaximal_of_mem_minimalPrimes_tensorProduct_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.not_isMaximal_of_mem_minimalPrimes_tensorProduct_rigidDataH1Pow), where it forces certain minimal primes not to be maximal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.snd_apply_eq_zero_of_mem_minimalPrimes_of_isMaximal
    (L : Type) [Field L] [CharZero L] (R : Type) [CommRing R] [Algebra L R] [IsReduced R]
    (𝔭 : Ideal R) (h𝔭 : 𝔭 ∈ (⊥ : Ideal R).minimalPrimes) (h𝔭' : 𝔭.IsMaximal)
    [Module.Finite L (R ⧸ 𝔭)]
    (K : Type) [Field K] [Algebra L K]
    (φ : R →ₐ[L] DualNumber K)
    (hφ : RingHom.ker ((TrivSqZeroExt.fstHom L K K).comp φ).toRingHom = 𝔭) :
    ∀ r : R, (φ r).snd = 0 := by sorry
