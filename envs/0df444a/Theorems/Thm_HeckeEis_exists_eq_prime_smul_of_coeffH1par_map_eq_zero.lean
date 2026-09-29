-- Prove2me | Theorems.Thm_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero
-- name    : HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/c0aac890-555f-5a85-9908-b587507df39a
-- title:
--   Kernel of mod-p reduction on parabolic cohomology is p-divisible
-- statement:
--   Fix $N \ge 1$, an integer $n \ge 0$, an odd prime $p$ with $p \nmid N$ and $n < p$, and a field $K$ of characteristic $p$. For a commutative ring $R$, let $\mathrm{BinaryForm}\,R\,n$ denote the submodule of homogeneous polynomials of degree $n$ in $R[X_0,X_1]$, on which [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61) makes $\mathrm{SL}_2(\mathbb Z)$ act by substituting for the variables the linear forms given by the columns of the matrix; restrict this representation to $\Gamma_0(N)$. Write $\mathrm{coeffH1par}$ for the quotient of the module of parabolic cocycles $z$ (that is, $z(gh) = z(g) + \rho(g) z(h)$ for all $g,h$, and $z(\gamma) \in \mathrm{range}(\rho(\gamma)-1)$ whenever $\mathrm{tr}(\gamma)^2 = 4$) by the submodule of those parabolic cocycles that are coboundaries. Let $\Phi$ be an additive map from the $\mathbb Z$-coefficient group $\mathrm{coeffH1par}$ to the $K$-coefficient one, assumed compatible with coefficient reduction in the following sense: for every integral parabolic cocycle $z$ there is a $K$-valued parabolic cocycle $w$ with $w(g)$ equal to the image of $z(g)$ under the coefficientwise map $\mathbb Z \to K$ for all $g \in \Gamma_0(N)$, and with $\Phi$ of the class of $z$ equal to the class of $w$. Then every $y$ in the integral group with $\Phi(y) = 0$ is of the form $p \cdot y'$ for some $y'$ in that group.
--
--   This is the injectivity of the reduction map $H^1_{\mathrm{par}}(\Gamma_0(N), \mathrm{Sym}^n\mathbb Z^2)/p \to H^1_{\mathrm{par}}(\Gamma_0(N), \mathrm{Sym}^n K^2)$ in the range $n < p$, $p \nmid N$, stated here as $p$-divisibility of the kernel and with the reduction map given abstractly by its compatibility with coefficient reduction on cocycles. It is used in the construction of mod-$p$ Hecke eigenclasses in parabolic cohomology for odd $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero (N : ℕ) [NeZero N] (n : ℕ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpN : ¬ p ∣ N) (hn : n < p)
    (K : Type*) [Field K] [CharP K p]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g : MvPolynomial (Fin 2) K)
            = MvPolynomial.map (Int.castRingHom K) (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w))
    (y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) (hy : Φ y = 0) :
    ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), y = (p : ℤ) • y' := by sorry
