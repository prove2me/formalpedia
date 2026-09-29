-- Prove2me | Theorems.Thm_HeckeEis_span_range_coeffH1par_map_int_complex_eq_top
-- name    : HeckeEis.span_range_coeffH1par_map_int_complex_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5eb40846-6d00-580e-ab3a-675e2c47753c
-- title:
--   Image of integral parabolic cohomology spans the complex one
-- statement:
--   Let $n$ and $N$ be natural numbers with $N \neq 0$, and write $\rho_K$ for the representation of $\Gamma_0(N)$ on the module $\mathrm{BinaryForm}\,K\,n$ of homogeneous polynomials of degree $n$ in two variables over $K$ obtained by restricting along the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ the action $\mathrm{binaryFormRepSL}$ of $\mathrm{SL}_2(\mathbb{Z})$ by linear substitution of the matrix entries. Here $\mathrm{coeffH1par}\,\rho_K$ denotes the quotient of the $K$-module of parabolic cocycles — functions $z \colon \Gamma_0(N) \to \mathrm{BinaryForm}\,K\,n$ satisfying $z(gh) = z(g) + \rho_K(g)(z(h))$ and, for every $\gamma$ whose image in $M_2(\mathbb{Z})$ has $(\mathrm{tr}\,\gamma)^2 = 4$, $z(\gamma) \in \mathrm{range}(\rho_K(\gamma) - 1)$ — by the submodule of those which are coboundaries, and $\mathrm{coeffH1parMk}$ the quotient map. Given an additive group homomorphism $\Phi \colon \mathrm{coeffH1par}\,\rho_{\mathbb{Z}} \to \mathrm{coeffH1par}\,\rho_{\mathbb{C}}$ with the property that for every integral parabolic cocycle $z$ there is a complex parabolic cocycle $w$ whose value at each $g \in \Gamma_0(N)$ is the coefficientwise image of $z(g)$ under the ring homomorphism $\mathbb{Z} \to \mathbb{C}$, and such that $\Phi$ sends the class of $z$ to the class of $w$, the conclusion is that the $\mathbb{C}$-span of the set-theoretic range of $\Phi$ is the whole of $\mathrm{coeffH1par}\,\rho_{\mathbb{C}}$.
--
--   This is the surjectivity half of the statement that parabolic group cohomology of $\Gamma_0(N)$ with coefficients in binary forms of degree $n$ admits an integral structure: the classes coming from integral parabolic cocycles generate the complex parabolic cohomology over $\mathbb{C}$. It is used in establishing an integral structure on spaces of cusp forms of weight at least two ([`CuspForm.hasIntegralStructure_of_two_le`](thm.html#CuspForm.hasIntegralStructure_of_two_le)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_span_range_coeffH1par_map_int_complex_eq_top.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.span_range_coeffH1par_map_int_complex_eq_top (n N : ℕ) [NeZero N]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
            = MvPolynomial.map (Int.castRingHom ℂ)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) :
    Submodule.span ℂ (Set.range Φ) = ⊤ := by sorry
