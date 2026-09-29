-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
-- name    : ModularCurve.JHNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/2362fc3e-3e2d-5ef4-9cb5-09fcdfe61cd3
-- title:
--   ψ-twist of the toric fibre differs by an integral map
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ lying over $p$ (that is, $p$ belongs to the nonunits of $A$), whose residue field $\kappa = \mathrm{ResidueField}(A)$ is of characteristic $p$ and algebraically closed. Let $\Lambda$ be level data in the sense of [`ModularCurve.JHNeronObjectAtP.LevelData`](def/ModularCurve_JHNeronObjectAtP.html#L32): a morphism $\sigma_A \colon \operatorname{Spec} A \to \mathrm{base}\ p$ lifting the generic point, a scheme $X$ with structure morphism $f$ to $\mathrm{base}\ p$, a relative group law on $f$ over $\mathrm{baseRing}\ p$, and bijections of $J_H(M/p)$-points with sections of $f$ over the generic point and of the degree-zero divisor class group of the reduction curve with sections of $f$ over $\mathrm{resPt}\ A \gg \sigma_A$. Assume $h_\Lambda$: $f$ is smooth and proper with connected fibres and admits a relative group law. Let $O$ be a Néron object for $J_H(M)$ at $p$ over these data, with structure morphism $g$, toric rank $t =$ `O.toricRank` and toric fibre morphism `O.torusFibre.1` out of $\operatorname{Spec}$ of the group algebra $\kappa[\mathbb{Z}^t]$ into the pullback $G_\kappa$ of $g$ along $\mathrm{resPt}\ A \gg \sigma_A$. Let $\psi$ be a ring automorphism of $\kappa$ and let $\Xi_G$ be an endomorphism of $G_\kappa$ which commutes with the first projection and whose composite with the second projection is the second projection followed by $\operatorname{Spec} \psi$. The assertion is that there exists an additive endomorphism $P_0$ of $\mathbb{Z}^t = (\mathrm{Fin}\ t \to \mathbb{Z})$ such that applying $\psi$ to the coefficients of $\kappa[\mathbb{Z}^t]$ and then `O.torusFibre.1` agrees with applying $P_0$ to the exponents of $\kappa[\mathbb{Z}^t]$, then `O.torusFibre.1`, then $\Xi_G$.
--
--   This is a rigidity statement for the maximal split subtorus of the geometric special fibre: twisting the coefficient field by an automorphism $\psi$ changes the toric fibre only by an integral endomorphism of the character lattice, since there are no nonconstant maps from a torus to an abelian quotient and the endomorphisms of a split torus are integral matrices. It feeds the computation, at $\ell = p$, of the actions of $U_p$ and of Frobenius on the toric Tate lattice of the Néron object of $J_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ψ : ResidueField ↥A ≃+* ResidueField ↥A)

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))
    :
    ∃ P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) ψ.toRingHom)) ≫ O.torusFibre.1 =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG := by sorry
