-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_torusPt_residue_toricLift_and_torusFibre_injective
-- name    : ModularCurve.JHNeronObjectAtP.exists_torusPt_residue_toricLift_and_torusFibre_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/e07d68f8-6cda-5bf6-b1e1-8160e9806537
-- title:
--   Toric lifts reduce to torus characters on the special fibre
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ (that is, $p$ lies in the nonunits of $A$), whose residue field $\kappa = \mathrm{ResidueField}\,A$ is of characteristic $p$ and algebraically closed. Let $\Lambda$ be level data at $A$ — a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec}(\mathbb{Z}_{(p)}$-localisation$)$ with $\mathrm{barPt}\,A \mathbin{\text{then}} \sigma_A = \mathrm{genPt}\,p$, together with a scheme with relative group law and parametrisations of its generic and special points — and let $O$ be a level-$\Gamma_H(M)$ Néron object for these data, with structure morphism $O.g$, relative group law $O.L$, toric rank $t = O.\mathrm{toricRank}$, toric lift $O.\mathrm{toricLift}$ and special-fibre torus point $O.\mathrm{torusFibre}$; let $m > 0$. The assertion is a conjunction of four statements. First, for every $A$-algebra map $\chi \colon A[(\mathbb{Z}/m)^t] \to A$ there is a $\kappa$-algebra map $\psi \colon \kappa[\mathbb{Z}^t] \to \kappa$ with $\psi(e_v) = \overline{\chi(e_{v \bmod m})}$ for all $v \in \mathbb{Z}^t$, such that $\operatorname{Spec}$ of $\mathrm{residue} \circ \chi$, followed by the underlying morphism of $O.\mathrm{toricLift}\,m$ and then the first projection of the pullback of $O.g$ along $\sigma_A$, equals the underlying morphism of the point obtained by composing $\mathrm{torusPt}\,\kappa\,t\,\psi$ with $O.\mathrm{torusFibre}$, followed by the first projection of the pullback of $O.g$ along $\mathrm{resPt}\,A \mathbin{\text{then}} \sigma_A$. Second, composition with $O.\mathrm{torusFibre}$ is injective on such characters $\psi$. Third, every point of $\mathrm{torusStr}\,\kappa\,t$ over the identity of $\operatorname{Spec}\kappa$ is $\mathrm{torusPt}\,\kappa\,t\,\psi$ for some $\psi$. Fourth, the character that is the unit of the convolution monoid structure (`WithConv`) on these characters is carried by $O.\mathrm{torusFibre}$ to the identity section of the group law $O.L$ base changed along $\mathrm{resPt}\,A \mathbin{\text{then}} \sigma_A$.
--
--   This records the compatibility between the $\mu_m^t$-level toric lift over $A$ and the split torus in the special fibre of the Néron object at $p$: $\kappa$-points of the split torus are exactly characters of the group algebra $\kappa[\mathbb{Z}^t]$, the torus embeds injectively and unitally, and reduction of a $\mu_m$-character is the character obtained by composing with $\mathbb{Z}^t \to (\mathbb{Z}/m)^t$. It is used in the comparison of the Frobenius and torus matrices attached to the $U_p$-operator on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_torusPt_residue_toricLift_and_torusFibre_injective.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.exists_torusPt_residue_toricLift_and_torusFibre_injective
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) :

    (∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
      ∃ ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
        (∀ v : Fin O.toricRank → ℤ, ψ (AddMonoidAlgebra.single v 1) =
            IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1))) ∧
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA =
          (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre).1 ≫
            pullback.fst O.g (resPt A ≫ Λ.σA)) ∧

    (∀ ψ ψ' : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
      NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre =
        NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ') O.torusFibre → ψ = ψ') ∧

    (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (torusStr (ResidueField ↥A) O.toricRank),
      ∃ ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
        y = torusPt (ResidueField ↥A) O.toricRank ψ) ∧

    NeronModelInfra.schemeHomOverComp
        (torusPt (ResidueField ↥A) O.toricRank
          (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv)
        O.torusFibre = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by sorry
