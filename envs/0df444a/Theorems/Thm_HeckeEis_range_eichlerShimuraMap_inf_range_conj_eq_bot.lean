-- Prove2me | Theorems.Thm_HeckeEis_range_eichlerShimuraMap_inf_range_conj_eq_bot
-- name    : HeckeEis.range_eichlerShimuraMap_inf_range_conj_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/08ca6524-3cdd-543d-8541-99b27558904b
-- title:
--   Injectivity half of Eichler–Shimura for Γ₀(N)
-- statement:
--   Let $N \ge 1$ and $n \ge 0$ be integers, and let $\rho$ denote the representation of $\Gamma_0(N)$ obtained by restricting to $\Gamma_0(N) \subseteq \mathrm{SL}(2,\mathbb{Z})$ the action of $\mathrm{SL}(2,\mathbb{Z})$ on the space of binary forms of degree $n$ over $\mathbb{C}$ (the homogeneous polynomials of degree $n$ in two variables) by linear substitution of the variables. Write $H = \mathrm{HeckeEis.coeffH1par}\,\rho$ for the quotient of the module of parabolic cocycles — functions $z \colon \Gamma_0(N) \to \mathrm{BinaryForm}$ with $z(gh) = z(g) + \rho(g) z(h)$ and with $z(\gamma) \in \mathrm{range}(\rho(\gamma) - 1)$ whenever the integral matrix of $\gamma$ has trace squared equal to $4$ — by those parabolic cocycles that are coboundaries. Assume given a $\mathbb{C}$-linear map $ES$ from the cusp forms of weight $(n : \mathbb{Z}) + 2$ on $\Gamma_0(N)$ to $H$ whose underlying function is [`HeckeEis.eichlerShimuraMap n N`](def/HeckeEis_EichlerIntegral.html#L114), and an additive endomorphism $\Phi$ of $H$ such that for every parabolic cocycle $z$ there is a parabolic cocycle $w$ with $w(g)$ equal to the coefficientwise complex conjugate of $z(g)$ for all $g \in \Gamma_0(N)$ and with $\Phi$ of the class of $z$ equal to the class of $w$. Then for cusp forms $f, g$ of weight $(n : \mathbb{Z}) + 2$ on $\Gamma_0(N)$, the equality $ES(f) = \Phi(ES(g))$ forces $f = 0$.
--
--   This is the disjointness, or injectivity, half of the Eichler–Shimura relation: the image of the Eichler–Shimura map on cusp forms of weight $n+2$ meets its complex conjugate only in zero inside parabolic cohomology with $\mathrm{Sym}^n$ coefficients. Combined with the bound on $\dim H^1_{\mathrm{par}}$ by twice the dimension of the space of cusp forms, it yields the direct sum decomposition recorded in [`HeckeEis.isCompl_range_eichlerShimuraMap_range_conj`](thm.html#HeckeEis.isCompl_range_eichlerShimuraMap_range_conj), the sole consumer of this statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_range_eichlerShimuraMap_inf_range_conj_eq_bot.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.range_eichlerShimuraMap_inf_range_conj_eq_bot (N : ℕ) [NeZero N] (n : ℕ)
    (ES : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hES : ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), ES f = HeckeEis.eichlerShimuraMap n N f)
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
            = MvPolynomial.map (starRingEnd ℂ)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (hfg : ES f = Φ (ES g)) : f = 0 := by sorry
