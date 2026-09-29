-- Prove2me | Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
-- name    : ModularCurve.coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/d97a11f9-4a29-5527-8c52-0600c012263a
-- title:
--   q-expansion of dy/y has ℓ-th power coefficients
-- statement:
--   Let $K$ be a field of characteristic $\ell$ for a prime $\ell$, and let $N\ge 1$. Write $F_N :=$ `modularFunctionFieldFullC K N` for the intermediate field of $K((q))$ obtained by adjoining to $K$ the set of Laurent series $\bar j(q^d)$, that is the images of `jqModC K` under the substitution $q\mapsto q^d$, for the nonzero divisors $d$ of $N$. Let `frobeniusModL K N ℓ` be the $K$-algebra endomorphism of $F_N$ induced by the substitution $q\mapsto q^{\ell}$ on $K((q))$. Let $f,y\in F_N$ satisfy $\mathrm{Frob}(y)=f^{\ell}$, where $\mathrm{Frob}$ is this endomorphism, and let $n\in\mathbb Z$. Consider `qExpansionDiffAlong` applied to the inclusion $F_N\hookrightarrow K((q))$: the $K$-linear map $\Omega_{F_N/K}\to K((q))$ determined, when one exists, by the two conditions $\varphi(Dx)=\theta(x)$ with $\theta=q\,d/dq$, and $\varphi(g\cdot\omega)=g\,\varphi(\omega)$ for $g\in F_N$ (and the zero map otherwise). The assertion is that the $n$-th coefficient of the image of the logarithmic differential $y^{-1}\,Dy$ equals the $\ell$-th power of the $n$-th coefficient of the image of $f^{-1}\,Df$. No non-vanishing hypothesis on $f$ or $y$ is imposed.
--
--   This is the coefficientwise compatibility of logarithmic differentials with Frobenius on the function field of the modular curve in characteristic $\ell$: the $q$-expansion of $dy/y$ is the coefficientwise $\ell$-th power of that of $df/f$ whenever $y(q^{\ell})=f(q)^{\ell}$. It feeds into [`ModularCurve.coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL`](thm.html#ModularCurve.coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL), the divisor-free core of the comparison between a function and its Frobenius pushforward.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
    (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (f y : modularFunctionFieldFullC K N) (hy : frobeniusModL K N ℓ y = f ^ ℓ) (n : ℤ) :
    (qExpansionDiffAlong (modularFunctionFieldFullC K N).val
        (y⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) y)).coeff n =
      ((qExpansionDiffAlong (modularFunctionFieldFullC K N).val
        (f⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) f)).coeff n) ^ ℓ := by sorry
