-- Prove2me | Theorems.Thm_HeckeEis_mem_span_range_coeffH1par_map_rat_complex
-- name    : HeckeEis.mem_span_range_coeffH1par_map_rat_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/dc7fa376-1f62-5cff-8bf9-4f6c2687e89a
-- title:
--   Rational classes span parabolic cohomology over ℂ
-- statement:
--   Fix $n \in \mathbb{N}$ and a finitely generated subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$. For a commutative ring $K$, let $\rho_{K}$ denote the representation of $\Gamma$ on the space [`HeckeEis.BinaryForm K n`](def/HeckeEis_BinaryFormRep.html#L25) of degree-$n$ homogeneous polynomials in two variables over $K$ obtained by restricting to $\Gamma$ the substitution action of $\mathrm{SL}_2(\mathbb{Z})$ given by [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61). Here [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho_K$ is the quotient of the $K$-module of parabolic cocycles — functions $z : \Gamma \to$ `BinaryForm K n` with $z(gh) = z(g) + \rho_K(g)(z(h))$ and with $z(\gamma) \in \mathrm{range}(\rho_K(\gamma) - 1)$ whenever the trace of $\gamma$, viewed as an integer matrix, satisfies $\mathrm{tr}(\gamma)^2 = 4$ — by the submodule of those parabolic cocycles that are coboundaries, and `coeffH1parMk` is the quotient map. Assume given an additive homomorphism $\Psi$ from `coeffH1par` $\rho_{\mathbb{Q}}$ to `coeffH1par` $\rho_{\mathbb{C}}$ with the following compatibility at cochain level: for every rational parabolic cocycle $z$ there is a complex parabolic cocycle $w$ such that for all $g \in \Gamma$ the polynomial $w(g)$ is the image of $z(g)$ under coefficientwise application of $\mathbb{Q} \to \mathbb{C}$, and $\Psi$ sends the class of $z$ to the class of $w$. The conclusion is that every element $X$ of `coeffH1par` $\rho_{\mathbb{C}}$ lies in the $\mathbb{C}$-span of the range of $\Psi$.
--
--   This is the statement that the parabolic cohomology $H^1_{\mathrm{par}}(\Gamma, \mathrm{Sym}^n)$ with complex coefficients is spanned over $\mathbb{C}$ by the image of its rational counterpart, in the concrete model where the coefficient module consists of binary forms acted on by substitution. It is used in the construction of a basis of the complex parabolic cohomology coming from the integral, hence rational, classes ([`HeckeEis.exists_basis_coeffH1par_int_complex`](thm.html#HeckeEis.exists_basis_coeffH1par_int_complex)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_span_range_coeffH1par_map_rat_complex (n : ℕ) (Γ : Subgroup SL(2, ℤ)) [Group.FG Γ]
    (Ψ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp Γ.subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype))
    (hΨ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℚ n).comp Γ.subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)),
        (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
            = MvPolynomial.map (algebraMap ℚ ℂ)
                (((z : Γ → ↥(HeckeEis.BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ))) ∧
        Ψ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (X : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)) :
    X ∈ Submodule.span ℂ (Set.range Ψ) := by sorry
