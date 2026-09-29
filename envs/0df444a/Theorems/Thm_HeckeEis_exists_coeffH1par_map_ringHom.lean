-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffH1par_map_ringHom
-- name    : HeckeEis.exists_coeffH1par_map_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/4a939097-2cd8-5000-a1e3-d6f0a5fa32b7
-- title:
--   Change of coefficients for parabolic H¹ of binary forms
-- statement:
--   Let $R$ and $R'$ be commutative rings, $\varphi\colon R\to R'$ a ring homomorphism, $n$ a natural number and $\Gamma$ any subgroup of $\mathrm{SL}_2(\mathbb Z)$. For a commutative ring $S$ let $\rho_S$ denote the representation of $\Gamma$ obtained by restricting along the inclusion $\Gamma\hookrightarrow \mathrm{SL}_2(\mathbb Z)$ the representation [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61) of $\mathrm{SL}_2(\mathbb Z)$ on the degree-$n$ homogeneous part $\mathrm{BinaryForm}\,S\,n$ of $S[X_0,X_1]$, where a matrix $M$ with integer entries acts by the substitution $X_j\mapsto \sum_i (M_{ij}\bmod S)\,X_i$. Here [`HeckeEis.coeffParabolicCocycles`](def/Gamma0CoeffCohomology.html#L75) $\rho_S$ is the $S$-submodule of maps $z\colon\Gamma\to \mathrm{BinaryForm}\,S\,n$ satisfying the cocycle identity $z(gh)=z(g)+\rho_S(g)z(h)$ and, for every $\gamma\in\Gamma$ whose underlying integer matrix has trace squared equal to $4$, the condition $z(\gamma)\in \mathrm{range}(\rho_S(\gamma)-1)$; [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho_S$ is its quotient by the coboundaries lying in it, with quotient map [`HeckeEis.coeffH1parMk`](def/Gamma0CoeffCohomology.html#L111). The assertion is that there exists an additive group homomorphism $\Phi$ from [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho_R$ to [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho_{R'}$ such that for every parabolic cocycle $z$ over $R$ there is a parabolic cocycle $w$ over $R'$ with $w(g)=\mathrm{MvPolynomial.map}\,\varphi\,(z(g))$ in $R'[X_0,X_1]$ for all $g\in\Gamma$, and $\Phi$ of the class of $z$ equals the class of $w$.
--
--   This is the coefficient-change map on parabolic cohomology with binary-form coefficients, induced by applying $\varphi$ to the coefficients of a cocycle; the existential formulation packages the map together with the fact that it is computed by coefficientwise pushforward of cocycle representatives. It is used in the construction of integral structures on spaces of cusp forms and in comparing bases and Hecke eigenclasses of $H^1_{\mathrm{par}}$ over different coefficient rings, such as $\mathbb Z$ and $\mathbb C$ or a ring and its reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1par_map_ringHom.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_map_ringHom {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ)
    (Γ : Subgroup SL(2, ℤ)) :
    ∃ Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp Γ.subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp Γ.subtype),
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp Γ.subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp Γ.subtype)),
        (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
            = MvPolynomial.map φ
                (((z : Γ → ↥(HeckeEis.BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w := by sorry
