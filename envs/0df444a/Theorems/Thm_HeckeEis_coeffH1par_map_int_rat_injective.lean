-- Prove2me | Theorems.Thm_HeckeEis_coeffH1par_map_int_rat_injective
-- name    : HeckeEis.coeffH1par_map_int_rat_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/21ed02fb-bd65-542e-9e28-747806cdc55f
-- title:
--   Injectivity of H¹ₚₐᵣ from ℤ to ℚ
-- statement:
--   Fix natural numbers $n$ and $N$ with $N \neq 0$. For a commutative ring $K$, let $\rho_K$ denote the representation of $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb Z)$ on the $K$-module of homogeneous polynomials of degree $n$ in two variables over $K$ obtained by restricting [`HeckeEis.binaryFormRepSL K n`](def/HeckeEis_BinaryFormRep.html#L61), whose value at a matrix $M$ is the substitution $X_j \mapsto \sum_i M_{ij} X_i$; write $Z_K$ for the submodule of parabolic cocycles, that is, maps $z : \Gamma_0(N) \to \mathrm{BinaryForm}\,K\,n$ with $z(gh) = z(g) + \rho_K(g)(z(h))$ for all $g,h$ and with $z(\gamma)$ in the range of $\rho_K(\gamma) - 1$ for every $\gamma$ whose underlying integral matrix has trace squared equal to $4$, and $H_K = Z_K / (Z_K \cap \text{coboundaries})$ for the corresponding quotient [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100), with $[\,\cdot\,]$ the quotient map [`HeckeEis.coeffH1parMk`](def/Gamma0CoeffCohomology.html#L111). Let $\Phi : H_{\mathbb Z} \to H_{\mathbb Q}$ be an additive group homomorphism such that for every parabolic cocycle $z \in Z_{\mathbb Z}$ there is a parabolic cocycle $w \in Z_{\mathbb Q}$ with $w(g)$ equal to the image of $z(g)$ under the coefficientwise map $\mathbb Z \to \mathbb Q$ on polynomials, for all $g \in \Gamma_0(N)$, and with $\Phi([z]) = [w]$. Then $\Phi$ is injective.
--
--   This is the injectivity of the base-change map $H^1_{\mathrm{par}}(\Gamma_0(N), \mathrm{Sym}^n) \to H^1_{\mathrm{par}}(\Gamma_0(N), \mathrm{Sym}^n \otimes \mathbb Q)$ on parabolic cohomology with binary-form coefficients, stated for any additive map induced on classes by coefficient extension of cocycles; it rests on the torsion-freeness statement [`HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero`](thm.html#HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero). It is used in the construction of a $\mathbb Z$-basis of the integral parabolic cohomology compatible with its complexification, [`HeckeEis.exists_basis_coeffH1par_int_complex`](thm.html#HeckeEis.exists_basis_coeffH1par_int_complex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffH1par_map_int_rat_injective.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffH1par_map_int_rat_injective (n N : ℕ) [NeZero N]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ)
            = MvPolynomial.map (Int.castRingHom ℚ)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) :
    Function.Injective Φ := by sorry
