-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
-- name    : ModularCurve.JHNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/438a933e-0eda-5f49-8331-f09583b9b92f
-- title:
--   Endomorphisms act on toric lifts through M₀ mod m
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (so $A$ lies over $p$) whose residue field is algebraically closed of characteristic $p$. Let $\Lambda$ be level data for $J_H$ at $p$ over $A$ — a structure morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec}(\mathbb{Z}\text{-localisation } \mathtt{baseRing}\,p)$ compatible with the generic point, a scheme $X$ with a morphism $f$ to that base carrying a relative group law, and bijections of the generic and special point groups with the corresponding sections of $f$ — and let $h\Lambda$ assert that $\Lambda.f$ is smooth, proper, with connected fibres and admits a relative group law. Let $O$ be a Néron object for $J_H(M)$ at $p$ attached to $\Lambda$, with structure morphism $g \colon G \to \mathtt{base}\,p$, toric rank $t = O.\mathtt{toricRank}$, special-fibre torus datum $O.\mathtt{torusFibre}$ and toric lifts $O.\mathtt{toricLift}\,m\,hm$. Let $\varphi$ be an endomorphism of $G$ over the base (a morphism $G \to G$ with $\varphi \circ g = g$ in the sense of $g$-over-$g$ morphisms) which is additive for the group law: for every $T \to \mathtt{base}\,p$ and all sections $x, y$ over $T$, the product $x \cdot y$ followed by $\varphi$ equals the product of $x$ followed by $\varphi$ and $y$ followed by $\varphi$. Let $M_0$ be an additive endomorphism of $\mathbb{Z}^t$ such that the morphism $\operatorname{Spec}$ of the domain-reindexing ring homomorphism $M_0$ of the residue-field monoid algebra, followed by $O.\mathtt{torusFibre}$, equals $O.\mathtt{torusFibre}$ followed by the restriction of $\varphi$ along $\mathtt{resPt}\,A \circ \sigma_A$ (the morphism induced on the pullback of $g$ by this base point). Let $m > 0$. Then there is an additive endomorphism $\bar{M}$ of $(\mathbb{Z}/m)^t$ which reduces $M_0$, in the sense that $\bar{M}$ composed after coordinatewise reduction $\mathbb{Z}^t \to (\mathbb{Z}/m)^t$ equals that reduction composed after $M_0$, and such that for every $A$-algebra homomorphism $\chi \colon A[(\mathbb{Z}/m)^t] \to \overline{\mathbb{Q}}$ the point $\mathtt{muPt}\,A\,t\,m\,\chi$ followed by the toric lift $O.\mathtt{toricLift}\,m\,hm$ and then by the restriction of $\varphi$ along $\sigma_A$ coincides with $\mathtt{muPt}\,A\,t\,m$ of $\chi \circ \mathtt{mapDomainAlgHom}\,\bar{M}$ followed by the same toric lift.
--
--   This is the rigidity statement transporting the integral matrix through which an additive endomorphism of the Néron object acts on its split special-fibre torus to the action on the $m$-torsion points of the toric lift, for a single $M_0$ and all $m > 0$ simultaneously, $p$-powers included: $\varphi$ acts on $\operatorname{Hom}((\mathbb{Z}/m)^t, \mu_m(\overline{\mathbb{Q}}))$ through $M_0 \bmod m$. It is used in the identification of the Hecke operator $U_p$ on toric points and in the computation of the Galois action on Tate parameters that underlies level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (φ : SchemeHomOver O.g O.g)
    (hφmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    (M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
        O.torusFibre.1 ≫ (fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φ).1)
    (m : ℕ) (hm : 0 < m) :
    ∃ Mbar : (Fin O.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m),
      Mbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)).comp M₀ ∧
      ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        NeronModelInfra.schemeHomOverComp
            (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (O.toricLift m hm))
            (fibreRestrictAlong Λ.σA O.g O.g φ) =
          NeronModelInfra.schemeHomOverComp
            (muPt A O.toricRank m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))) (O.toricLift m hm) := by sorry
