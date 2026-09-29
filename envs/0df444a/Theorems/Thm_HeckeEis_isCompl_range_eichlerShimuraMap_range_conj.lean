-- Prove2me | Theorems.Thm_HeckeEis_isCompl_range_eichlerShimuraMap_range_conj
-- name    : HeckeEis.isCompl_range_eichlerShimuraMap_range_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5fd6c717-6136-56cd-8686-553176500925
-- title:
--   Eichler–Shimura: images of ES and ̄ES are complementary
-- statement:
--   Fix $N\ge 1$ and $n\ge 0$, and let $V_n$ be the space of homogeneous binary forms of degree $n$ over $\mathbb{C}$, carrying the representation of $\Gamma_0(N)\le \mathrm{SL}_2(\mathbb{Z})$ by substitution of the matrix into the variables, and let $H$ be the associated parabolic cohomology [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100): the quotient of the space of cocycles $z\colon\Gamma_0(N)\to V_n$ (i.e. $z(gh)=z(g)+g\cdot z(h)$) that are parabolic (for every $\gamma$ with $(\operatorname{tr}\gamma)^2=4$, $z(\gamma)$ lies in the image of $\rho(\gamma)-1$) by those parabolic cocycles which are coboundaries. Assume given: a $\mathbb{C}$-linear map $ES$ from $S_{n+2}(\Gamma_0(N))$ (the cusp forms of weight $(n:\mathbb{Z})+2$) to $H$ agreeing pointwise with [`HeckeEis.eichlerShimuraMap n N`](def/HeckeEis_EichlerIntegral.html#L114), the class of the cocycle of an Eichler integral of $f$ with parabolic cocycle (and $0$ if none exists); an additive endomorphism $\Phi$ of $H$ such that each parabolic cocycle $z$ admits a parabolic cocycle $w$ with $w(g)$ the coefficientwise complex conjugate of $z(g)$ for all $g$ and $\Phi[z]=[w]$; and a $\mathrm{starRingEnd}\,\mathbb{C}$-semilinear (conjugate-linear) map $ESbar$ with $ESbar(f)=\Phi(ES(f))$ for all $f$. The conclusion is that the ranges of $ES$ and of $ESbar$ are complementary submodules of $H$: their intersection is $0$ and their sum is all of $H$.
--
--   This is the Eichler–Shimura isomorphism in its decomposition form, $H^1_{\mathrm{par}}(\Gamma_0(N),V_n)=\mathrm{ES}(S_{n+2})\oplus\overline{\mathrm{ES}}(S_{n+2})$, stated for an abstract pair $(ES,\Phi)$ satisfying the defining properties of the Eichler–Shimura map and of coefficientwise conjugation. It is the analytic input to [`HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime`](thm.html#HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime), which packages the map together with its injectivity, the conjugation and Hecke equivariance at all primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isCompl_range_eichlerShimuraMap_range_conj.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isCompl_range_eichlerShimuraMap_range_conj (N : ℕ) [NeZero N] (n : ℕ)
    (ES : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hES : ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), ES f = HeckeEis.eichlerShimuraMap n N f)
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
            = MvPolynomial.map (starRingEnd ℂ)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (ESbar : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₛₗ[starRingEnd ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hESbar : ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), ESbar f = Φ (ES f)) :
    IsCompl (LinearMap.range ES) (LinearMap.range ESbar) := by sorry
