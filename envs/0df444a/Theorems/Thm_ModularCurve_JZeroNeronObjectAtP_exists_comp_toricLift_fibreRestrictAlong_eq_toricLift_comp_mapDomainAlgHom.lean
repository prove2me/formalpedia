-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/18985062-2b98-5242-b484-0d8f9df33a06
-- title:
--   Endomorphisms act on toric lifts through M₀ mod m
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, $p \nmid N_0$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that the image of $p$ lies in the nonunits of $A$. Let $\Lambda$ be a `LevelData` for $(N_0,p,A)$ satisfying `IsJacobian`, and let $O$ be a `JZeroNeronObjectAtP` for these data, with structure morphism $g \colon G \to \operatorname{Spec}(\text{baseRing } p)$, relative group law $O.L$, toric rank $t = O.{\tt toricRank}$, split-torus special fibre datum $O.{\tt torusFibre}$ and toric lifts $O.{\tt toricLift}\, m$. Let $\varphi$ be a morphism $G \to G$ over the base (i.e. $\varphi$ followed by $g$ is $g$) which is multiplicative: for every scheme $T$, every $s \colon T \to \operatorname{Spec}(\text{baseRing } p)$ and all $T$-points $x,y$ of $g$ over $s$, composing $O.L.\mathrm{mul}\,s\,x\,y$ with $\varphi$ gives $O.L.\mathrm{mul}\,s$ of the composites. Let $M_0$ be an additive endomorphism of $\mathbb{Z}^t$ such that the endomorphism $\operatorname{Spec}$ of the induced map of monoid algebras $\kappa(A)[\mathbb{Z}^t]$, followed by $O.{\tt torusFibre}$, equals $O.{\tt torusFibre}$ followed by the restriction of $\varphi$ to the fibre along $\mathrm{resPt}\,A$ followed by $\Lambda.\sigma_A$. Then for every $m > 0$ there is an additive endomorphism $\bar M$ of $(\mathbb{Z}/m)^t$ whose composite with coordinatewise reduction $\mathbb{Z}^t \to (\mathbb{Z}/m)^t$ equals the reduction of $M_0$, such that for every $A$-algebra homomorphism $\chi \colon A[(\mathbb{Z}/m)^t] \to \overline{\mathbb{Q}}$ the point $\mathrm{muPt}\,A\,t\,m\,\chi$ composed with the toric lift and then with the restriction of $\varphi$ to the fibre along $\Lambda.\sigma_A$ coincides with $\mathrm{muPt}\,A\,t\,m$ of $\chi$ precomposed with the algebra map induced by $\bar M$, composed with the toric lift.
--
--   This is the rigidity statement transporting the action of an endomorphism of the Néron object on the split torus of the special fibre to its action on the toric lifts $\mu_m^t$ over $A$, uniformly in $m$ (powers of $p$ included): a single integral matrix $M_0$ governs all levels, and the endomorphism permutes the toric $m$-torsion characters by the transpose of $M_0 \bmod m$. It is used in the computation of the Frobenius and Hecke matrices on the toric part, in particular by [`ModularCurve.JZeroNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint`](thm.html#ModularCurve.JZeroNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint) and by the two statements identifying Hecke and Frobenius actions on toric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
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
