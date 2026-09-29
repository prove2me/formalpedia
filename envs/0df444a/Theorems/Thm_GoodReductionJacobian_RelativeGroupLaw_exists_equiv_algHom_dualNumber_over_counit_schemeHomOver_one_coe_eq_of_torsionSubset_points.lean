-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_algHom_dualNumber_over_counit_schemeHomOver_one_coe_eq_of_torsionSubset_points
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_equiv_algHom_dualNumber_over_counit_schemeHomOver_one_coe_eq_of_torsionSubset_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/4a102f1e-d199-5d14-8a9b-f804efaed5ac
-- title:
--   Dual number points over the unit are p-torsion tangent vectors
-- statement:
--   Fix a prime $p$ and write $R = \mathrm{ratLocalizedAt}\;p$ for the subring of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $f \colon J \to \operatorname{Spec} R$ be a scheme over $R$ equipped with a relative group law $L$, that is, a group structure on the set $\mathrm{SchemeHomOver}\;t\;f$ of morphisms $T \to J$ commuting with $t \colon T \to \operatorname{Spec} R$, given by operations $L.\mathrm{mul}$, $L.\mathrm{one}$, $L.\mathrm{inv}$ satisfying the group axioms and natural in $T$. Let $H$ be a commutative Hopf $R$-algebra, and suppose given, for every commutative $R$-algebra $T$, a bijection $e_T$ from the $R$-algebra homomorphisms $H \to T$ with their convolution product onto the subset of $x \in \mathrm{SchemeHomOver}\;(\operatorname{Spec} T \to \operatorname{Spec} R)\;f$ with $L.\mathrm{nsmul}\;p\;x = L.\mathrm{one}$, such that $e_T$ carries the convolution product to $L.\mathrm{mul}$ and is natural: for an $R$-algebra map $g \colon T \to T'$ and $\varphi \colon H \to T$, the morphism attached to $g \circ \varphi$ is $\operatorname{Spec} g$ followed by the morphism attached to $\varphi$. Let $k$ be a field which is an $R$-algebra with $\operatorname{char} k = p$. The conclusion asserts the existence of a bijection $c$ from the set of $R$-algebra maps $D \colon H \to k[\epsilon]/(\epsilon^2)$ whose first component sends each $h \in H$ to the image in $k$ of the counit $\varepsilon(h)$, onto the set of morphisms $x \colon \operatorname{Spec} k[\epsilon]/(\epsilon^2) \to J$ over $R$ whose restriction along the projection $k[\epsilon]/(\epsilon^2) \to k$ is the unit section $L.\mathrm{one}$ over $k$, such that $c(D)$ is the morphism $e_{k[\epsilon]/(\epsilon^2)}(D)$ for every such $D$.
--
--   This is the statement that, in characteristic $p$, the tangent space at the identity of the $p$-torsion subgroup scheme $\operatorname{Spec} H$ exhausts the tangent space at the origin of $J$ over $k$, as in Mazur's analysis of the Eisenstein ideal; the bijection is realised literally by the given parametrisation $e$ at the dual numbers, so it transports the group structure as well. It is used in the computation of the cotangent space of the Jacobian model at the origin in terms of the $p$-torsion lattice ([`ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq`](thm.html#ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_algHom_dualNumber_over_counit_schemeHomOver_one_coe_eq_of_torsionSubset_points.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_equiv_algHom_dualNumber_over_counit_schemeHomOver_one_coe_eq_of_torsionSubset_points
    (p : ℕ) [Fact p.Prime]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt p) f)
    (H : Type) [CommRing H] [HopfAlgebra ↥(GaloisRep.ratLocalizedAt p) H]
    (e : ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T],
      WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T) ≃
        L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) T))) p)
    (hmul : ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (φ ψ : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) =
        L.mul _ (e T φ).val (e T ψ).val)
    (hnat : ∀ (T T' : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] [CommRing T'] [Algebra ↥(GaloisRep.ratLocalizedAt p) T']
        (g : T →ₐ[↥(GaloisRep.ratLocalizedAt p)] T') (φ : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
      ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1)
    (k : Type) [Field k] [Algebra ↥(GaloisRep.ratLocalizedAt p) k] [CharP k p] :
    ∃ c : {D : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) =
              algebraMap ↥(GaloisRep.ratLocalizedAt p) k (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H h)} ≃
          {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber k)))) f //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) k)))).1},
      ∀ D : {D : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) =
              algebraMap ↥(GaloisRep.ratLocalizedAt p) k (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H h)},
        (c D).1 = (e (DualNumber k) D.1).val := by sorry
