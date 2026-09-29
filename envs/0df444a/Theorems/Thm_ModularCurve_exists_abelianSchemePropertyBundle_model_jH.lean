-- Prove2me | Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
-- name    : ModularCurve.exists_abelianSchemePropertyBundle_model_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/84b403f2-df62-5e98-a5cb-cc47942fc2f3
-- title:
--   Good-reduction abelian-scheme model of J_H(M) at ℓ∤ M
-- statement:
--   Let $M\ge 1$ be an integer, $H\le(\mathbb Z/M)^\times$ a subgroup, and $\ell$ a prime not dividing $M$; write $\mathbb Z_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of rationals whose denominator is coprime to $\ell$, $J_H(M)=$ `JH M H` for the group of degree-zero divisor classes $\mathrm{Pic}^0$ of the function field `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$, and $J_H(M)(\kappa)=$ `JHC M H κ` for the corresponding $\mathrm{Pic}^0$ of `xHFunctionFieldC κ M H` over a field $\kappa$. The assertion is that there exist a scheme $J$, a morphism $f\colon J\to\operatorname{Spec}\mathbb Z_{(\ell)}$, a relative group law $L$ on $f$ (functorial group structures `mul`, `one`, `inv` on the sets $\{\varphi\colon T\to J\mid \varphi\text{ followed by }f=t\}$ of $T$-points over each $t\colon T\to\operatorname{Spec}\mathbb Z_{(\ell)}$, with associativity, unit, inverse and naturality under base change), and a bijection $\mathrm{pts}$ from $J_H(M)$ onto the set of points of $J$ over the structure morphism $\operatorname{Spec}\overline{\mathbb Q}\to\operatorname{Spec}\mathbb Z_{(\ell)}$, such that: $f$ satisfies `AbelianSchemePropertyBundle`, i.e. is smooth and proper with connected fibres and admits a relative group law; $L$ is commutative on $T$-points for every $T$ and every $t$; $\mathrm{pts}$ is additive; $\mathrm{pts}$ is Galois-equivariant, in that for $\sigma\in\operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)$ the morphism underlying $\mathrm{pts}(\sigma\cdot x)$ is $\operatorname{Spec}\sigma$ followed by the morphism underlying $\mathrm{pts}(x)$; and, for every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ and satisfying the predicate `ReductionInputsQExpModL` for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb Z)$ (existence of a reduction map on places of the relevant $q$-expansion function fields from characteristic zero to the residue field of $A$, with the integrality property recorded there), there are a morphism $\sigma_A\colon\operatorname{Spec}A\to\operatorname{Spec}\mathbb Z_{(\ell)}$, a bijection $\mathrm{pts}_A$ from $J_H(M)$ onto the points of $J$ over $\operatorname{Spec}\overline{\mathbb Q}\to\operatorname{Spec}A$ followed by $\sigma_A$, and a bijection $\mathrm{pts}_{\mathrm{sp}}$ from $J_H(M)(\kappa_A)$, $\kappa_A$ the residue field of $A$, onto the points of $J$ over $\operatorname{Spec}\kappa_A\to\operatorname{Spec}A$ followed by $\sigma_A$, such that $\mathrm{pts}_A(x)$ and $\mathrm{pts}(x)$ have the same underlying morphism for all $x$, $\mathrm{pts}_{\mathrm{sp}}$ is additive, and every $x\in J_H(M)$ is the restriction of an $A$-valued point $x_A$ of $J$ over $\sigma_A$ whose composite with $\operatorname{Spec}\overline{\mathbb Q}\to\operatorname{Spec}A$ is $\mathrm{pts}_A(x)$ and whose composite with $\operatorname{Spec}\kappa_A\to\operatorname{Spec}A$ is $\mathrm{pts}_{\mathrm{sp}}$ of the class `reductionQExpModL A (CohCarrier.GammaH M H) x`.
--
--   This is the statement that the modular curve $X_H(M)$ has good reduction at a prime $\ell\nmid M$ in the form needed downstream: its Jacobian $J_H(M)$ extends to a smooth proper group scheme with connected fibres over $\mathbb Z_{(\ell)}$, together with dictionaries between the $\overline{\mathbb Q}$-points and the degree-zero divisor classes of the $q$-expansion function field, between the $\kappa_A$-points and the classes in characteristic $\ell$, and the compatibility of these with the reduction map on divisor classes. It is used by [`ModularCurve.surjOn_reductionQExpModL_gammaH_torsion_pow`](thm.html#ModularCurve.surjOn_reductionQExpModL_gammaH_torsion_pow) to transfer torsion surjectivity statements to characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry GoodReductionJacobian ModularCurve IsLocalRing
open NeronModelInfra

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_abelianSchemePropertyBundle_model_jH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    ∃ (J : Scheme.{0})
      (f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
      (pts : JH M H ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f),
      AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
        (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) ∧
      (∀ x y : JH M H, pts (x + y) = L.mul _ (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ReductionInputsQExpModL A (CohCarrier.GammaH M H) →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (ptsA : JH M H ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) f)
          (ptsSp : JHC M H (ResidueField ↥A) ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f),
          (∀ x : JH M H, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JHC M H (ResidueField ↥A), ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v)) ∧
          ∀ x : JH M H, ∃ xA : SchemeHomOver σA f,
            GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) rfl xA =
              ptsA x ∧
            GoodReductionJacobian.schemeHomOverComp
                (Spec.map (CommRingCat.ofHom (residue ↥A))) rfl xA =
              ptsSp (reductionQExpModL A (CohCarrier.GammaH M H) x)) := by sorry
