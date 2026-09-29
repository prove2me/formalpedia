-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_heckeBetaModLH
-- name    : ModularCurve.finrankAlong_heckeBetaModLH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/faa6956f-f0da-532a-95e6-b42d035d7f61
-- title:
--   Degree of the degeneracy map q↦ q^ℓ on X_{H'}(N)
-- statement:
--   Let $K$ be an algebraically closed field, $N\ge 1$ a natural number, $H'$ a subgroup of $(\mathbb{Z}/N)^{\times}$ and $\ell$ a prime, and assume that the images of $N$ and of $\ell$ in $K$ are nonzero. Write $\Gamma_{H'}(N)$ for the subgroup [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, the image under the inclusion $\Gamma_0(N)\hookrightarrow\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under the character `gamma0Units N`, and for a subgroup $\Gamma$ write $\bar F(\Gamma)$ for [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101), the intermediate field of $K((q))$ (Laurent series, i.e. Hahn series over $K$ with value group $\mathbb{Z}$) generated over $K$ by the set `intFormRatiosC K Γ`. Assume the hypothesis [`ModularCurve.HeckeBetaModLHDefined K N H' ℓ`](def/ModularCurve_XHDifferentialsModL.html#L143): for every $y\in\bar F(\Gamma_{H'}(N))$ the substitution $q\mapsto q^{\ell}$, given by the ring homomorphism `qExpand K ℓ` which multiplies all exponents by $\ell$, carries $y$ into $\bar F(\Gamma_{H'}(N)\cap\Gamma_0(N\ell))$. Then the $K$-algebra map $\beta=$ `heckeBetaModLH`, which under this hypothesis is $x(q)\mapsto x(q^{\ell})$ from $\bar F(\Gamma_{H'}(N))$ to $\bar F(\Gamma_{H'}(N)\cap\Gamma_0(N\ell))$, has [`AlgebraicCurve.finrankAlong`](def/AlgebraicCurve_Correspondence.html#L51) equal to $\ell$ if $\ell\mid N$ and to $\ell+1$ otherwise; that is, the rank of the target as a module over the source along $\beta$, equivalently the degree of $\bar F(\Gamma_{H'}(N)\cap\Gamma_0(N\ell))$ over the image $\beta(\bar F(\Gamma_{H'}(N)))$, takes these values.
--
--   This is the degree of the second degeneracy map $X(\Gamma_{H'}(N)\cap\Gamma_0(N\ell))\to X(\Gamma_{H'}(N))$ coming from $\tau\mapsto\ell\tau$, in the $q$-expansion model of the modular function field over an algebraically closed field in which $N\ell$ is invertible; the case split $\ell$ versus $\ell+1=\#\mathbb{P}^1(\mathbb{F}_\ell)$ is the familiar index computation for $\Gamma_0(N\ell)$ inside $\Gamma_0(N)$. It is used in the computation of the $q$-expansion coefficients of the trace along $\beta$, which enters the description of the Hecke operator at $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_heckeBetaModLH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finrankAlong_heckeBetaModLH
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ) :
    AlgebraicCurve.finrankAlong K (ModularCurve.heckeBetaModLH K N H' ℓ) =
      if ℓ ∣ N then ℓ else ℓ + 1 := by sorry
