-- Prove2me | Theorems.Thm_HeckeEis_exists_ne_zero_smul_eq_coeffH1par_map_int_rat
-- name    : HeckeEis.exists_ne_zero_smul_eq_coeffH1par_map_int_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5d43ce16-6cb1-5176-9b4c-6033bc24cf48
-- title:
--   Rational parabolic classes have nonzero integral multiples
-- statement:
--   Fix natural numbers $n$ and $N$ with $N \neq 0$, and write $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$. For a commutative ring $K$, let $\rho_K$ denote the representation [`HeckeEis.binaryFormRepSL K n`](def/HeckeEis_BinaryFormRep.html#L61) of $\mathrm{SL}_2(\mathbb{Z})$ on the degree-$n$ homogeneous part of $K[X_0,X_1]$, where a matrix $M$ acts by the substitution $X_j \mapsto \sum_i M_{ij} X_i$, restricted along the inclusion of $\Gamma_0(N)$; and let $H^1_{\mathrm{par}}(\Gamma_0(N), \rho_K)$ be [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) of that representation, namely the quotient of the $K$-module of cocycles $z \colon \Gamma_0(N) \to \rho_K$ (so $z(gh) = z(g) + \rho_K(g) z(h)$) satisfying $z(\gamma) \in \mathrm{im}(\rho_K(\gamma) - 1)$ for every $\gamma$ whose matrix has trace squared equal to $4$, by the submodule of those which are coboundaries. Let $\Phi$ be an additive homomorphism from $H^1_{\mathrm{par}}(\Gamma_0(N), \rho_{\mathbb{Z}})$ to $H^1_{\mathrm{par}}(\Gamma_0(N), \rho_{\mathbb{Q}})$ which is assumed to be induced by coefficient extension at cochain level: for every integral parabolic cocycle $z$ there is a rational parabolic cocycle $w$ with $w(g)$ the image of $z(g)$ under the coefficient map $\mathbb{Z} \to \mathbb{Q}$ on polynomials, for all $g \in \Gamma_0(N)$, and with $\Phi$ of the class of $z$ equal to the class of $w$. Then for every class $x$ in $H^1_{\mathrm{par}}(\Gamma_0(N), \rho_{\mathbb{Q}})$ there exist a nonzero integer $m$ and a class $y$ in $H^1_{\mathrm{par}}(\Gamma_0(N), \rho_{\mathbb{Z}})$ with $\Phi(y) = m \cdot x$.
--
--   This says that the integral parabolic cohomology of $\Gamma_0(N)$ with symmetric-power coefficients spans the rational one, i.e. that the image of $\Phi$ is of finite index in the sense that every rational class becomes integral after multiplication by a suitable nonzero integer. It is used in the construction of a basis of $H^1_{\mathrm{par}}$ over $\mathbb{C}$ coming from the integral classes, in [`HeckeEis.exists_basis_coeffH1par_int_complex`](thm.html#HeckeEis.exists_basis_coeffH1par_int_complex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_ne_zero_smul_eq_coeffH1par_map_int_rat.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_ne_zero_smul_eq_coeffH1par_map_int_rat (n N : ℕ) [NeZero N]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N,
            ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ)
              = MvPolynomial.map (Int.castRingHom ℚ)
                  (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    ∃ (m : ℤ) (y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      m ≠ 0 ∧ Φ y = m • x := by sorry
