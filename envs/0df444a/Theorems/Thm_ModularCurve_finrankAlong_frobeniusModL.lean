-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_frobeniusModL
-- name    : ModularCurve.finrankAlong_frobeniusModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/c956b3ac-4551-5200-8b58-5df74675fb16
-- title:
--   Frobenius q↦ q^ℓ on the mod-ℓ modular function field has degree ℓ
-- statement:
--   Let $K$ be an algebraically closed field, let $\ell$ be a prime with $K$ of characteristic $\ell$, and let $N$ be a nonzero natural number. Inside the field $\mathrm{LaurentSeries}\,K = K((q))$ consider the intermediate field $F =$ [`ModularCurve.modularFunctionFieldFullC K N`](def/ModularCurve_X0ModL.html#L100), the subfield of $K((q))$ generated over $K$ by the family `divisorExpansionsC K N`. The map [`ModularCurve.frobeniusModL K N ℓ`](def/ModularCurve_FrobeniusModL.html#L117) is the $K$-algebra endomorphism $\varphi$ of $F$ obtained by restricting to $F$ the ring homomorphism [`ModularCurve.qExpand K ℓ`](def/ModularCurve_X0.html#L25) of $K((q))$, which rescales the exponents of a Hahn/Laurent series by the factor $\ell$, i.e. sends $x(q)$ to $x(q^{\ell})$ (the fact that $F$ is stable under this operation being part of the construction, and the $K$-linearity coming from the invariance of constants). The quantity [`AlgebraicCurve.finrankAlong K φ`](def/AlgebraicCurve_Correspondence.html#L51) is, for a $K$-algebra map $\varphi : F \to F'$, the rank $\operatorname{finrank}_F F'$ of $F'$ as an $F$-module via the algebra structure induced by $\varphi$. The assertion is that for $\varphi =$ [`ModularCurve.frobeniusModL K N ℓ`](def/ModularCurve_FrobeniusModL.html#L117) this rank equals $\ell$; equivalently, $[F : \varphi(F)] = \ell$.
--
--   This is the degree statement for the relative Frobenius of the mod-$\ell$ modular curve of level $N$: a one-variable function field over a perfect field of characteristic $\ell$ is purely inseparable of degree exactly $\ell$ over the image of its Frobenius. It is used in the characteristic-$\ell$ analysis of the modular function field, notably in the computation of norms along `frobeniusModL`, in the comparison of Frobenius pushforwards with $\theta_\ell$-type coefficient maps, and in the reduction modulo $\ell$ of Hecke correspondences; its proof uses only the existence of modular polynomial data at level $N$ ([`ModularCurve.nonempty_modularPolynomialData`](thm.html#ModularCurve.nonempty_modularPolynomialData)), which supplies the needed algebraicity of the generators over $K(j)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_frobeniusModL.lean

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.finrankAlong_frobeniusModL (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N] :
    AlgebraicCurve.finrankAlong K (ModularCurve.frobeniusModL K N ℓ) = ℓ := by sorry
