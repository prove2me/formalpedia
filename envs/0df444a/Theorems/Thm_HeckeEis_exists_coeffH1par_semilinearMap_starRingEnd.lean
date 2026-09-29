-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffH1par_semilinearMap_starRingEnd
-- name    : HeckeEis.exists_coeffH1par_semilinearMap_starRingEnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/30dc3b73-51ef-56f4-b600-cad9e6be75e4
-- title:
--   A conjugate-linear involution on parabolic cohomology
-- statement:
--   Let $n$ be a natural number and let $\Gamma$ be any subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Write $\rho$ for the restriction along the inclusion $\Gamma \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the representation [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) of $\mathrm{SL}_2(\mathbb{Z})$ on the space [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) of degree-$n$ homogeneous polynomials in two variables over $\mathbb{C}$, in which a matrix $M$ acts by the substitution $X_j \mapsto \sum_i M_{ij} X_i$. Recall that [`HeckeEis.coeffParabolicCocycles`](def/Gamma0CoeffCohomology.html#L75) $\rho$ consists of the functions $z : \Gamma \to$ `BinaryForm ℂ n` satisfying $z(gh) = z(g) + \rho(g)(z(h))$ and, for every $\gamma \in \Gamma$ whose underlying integral matrix has $\operatorname{tr}(\gamma)^2 = 4$, $z(\gamma) \in \operatorname{range}(\rho(\gamma) - 1)$; and that [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho$ is the quotient of this module by the preimage of the coboundaries, with [`HeckeEis.coeffH1parMk`](def/Gamma0CoeffCohomology.html#L111) the quotient map. The assertion is that there exists a map $\Phi$ from [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho$ to itself which is semilinear over the complex conjugation $\mathrm{starRingEnd}\ \mathbb{C}$ (additive, with $\Phi(c \cdot x) = \bar{c} \cdot \Phi(x)$), such that (i) for every parabolic cocycle $z$ there is a parabolic cocycle $w$ with $w(g)$ equal to the coefficientwise complex conjugate `MvPolynomial.map (starRingEnd ℂ)` of $z(g)$ for all $g \in \Gamma$, and $\Phi$ sends the class of $z$ to the class of $w$; and (ii) $\Phi(\Phi(x)) = x$ for all $x$.
--
--   This provides the complex conjugation acting on the parabolic cohomology $H^1_{\mathrm{par}}(\Gamma, \mathrm{Sym}^n\mathbb{C}^2)$, realised on cocycles by coefficientwise conjugation of binary forms, which is available because the $\Gamma$-action is by substitutions with integral coefficients. It is used in the Eichler–Shimura part of the development, where the holomorphic and antiholomorphic images of the Eichler–Shimura map are compared, in [`HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime`](thm.html#HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime) and [`HeckeEis.isCompl_range_eichlerShimuraMap_range_conj`](thm.html#HeckeEis.isCompl_range_eichlerShimuraMap_range_conj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1par_semilinearMap_starRingEnd.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_semilinearMap_starRingEnd (n : ℕ) (Γ : Subgroup SL(2, ℤ)) :
    ∃ Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) →ₛₗ[starRingEnd ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype),
      (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)),
        ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)),
          (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
              = MvPolynomial.map (starRingEnd ℂ)
                  (((z : Γ → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ))) ∧
          Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
      ∀ x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype), Φ (Φ x) = x := by sorry
