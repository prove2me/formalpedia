-- Prove2me | Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jZero
-- name    : ModularCurve.exists_abelianSchemePropertyBundle_model_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/751eb1fa-6473-5437-bf26-b8311d621b25
-- title:
--   Abelian scheme model of J₀(p) over ℤ_{(ℓ)}
-- statement:
--   Let $p$ be a nonzero natural number (the level), $\ell$ a prime with $\ell \nmid p$, and write $R =$ [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$ for the subring of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $\ell$. The assertion is the existence of a scheme $J$, a morphism $f \colon J \to \operatorname{Spec} R$, a relative group law $L$ on $f$ (functorial operations `mul`, `one`, `inv` on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to J \mid \varphi \circ f = t\}$ for all $t \colon T \to \operatorname{Spec} R$, satisfying the group axioms and compatible with base change along morphisms $\psi$ over $\operatorname{Spec} R$), and a bijection $\mathrm{pts}$ from $\mathrm{JZero}\,p$, the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field of level $p$ base-changed to $\overline{\mathbf{Q}}$, to the set of points of $J$ over $\operatorname{Spec} \overline{\mathbf{Q}} \to \operatorname{Spec} R$, such that: (i) `AbelianSchemePropertyBundle` holds for $f$, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} R$ is connected, and $f$ admits a relative group law; (ii) $L$ is commutative on $T$-points for every $t \colon T \to \operatorname{Spec} R$; (iii) $\mathrm{pts}$ is additive for $L$; (iv) for every $\mathbf{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbf{Q}}$ and every $x$, the morphism underlying $\mathrm{pts}(\sigma \cdot x)$ is $\operatorname{Spec}(\sigma)$ followed by the morphism underlying $\mathrm{pts}(x)$; and (v) for every valuation subring $A$ of $\overline{\mathbf{Q}}$ with $\ell$ a non-unit of $A$ and satisfying `ReductionInputsModL A p` (existence of a place-reduction map along the residue map of $A$ together with the integral-generation condition on principal divisors), there are a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} R$, a bijection $\mathrm{pts}_A$ from $\mathrm{JZero}\,p$ to the points of $J$ over $\operatorname{Spec} \overline{\mathbf{Q}} \to \operatorname{Spec} A \to \operatorname{Spec} R$, and a bijection $\mathrm{pts}_{\mathrm{sp}}$ from $\mathrm{JZeroC}(\kappa_A)\,p$, the degree-zero divisor class group of the level-$p$ modular function field over the residue field $\kappa_A$ of $A$, to the points of $J$ over $\operatorname{Spec} \kappa_A \to \operatorname{Spec} A \to \operatorname{Spec} R$, such that $\mathrm{pts}_A$ has the same underlying morphisms as $\mathrm{pts}$, $\mathrm{pts}_{\mathrm{sp}}$ is additive for $L$, and `ReductionOfPointsAgreesModL` holds: each $x \in \mathrm{JZero}\,p$ is the restriction to $\overline{\mathbf{Q}}$ of an $A$-point of $J$ over $\sigma_A$ whose restriction to $\kappa_A$ is $\mathrm{pts}_{\mathrm{sp}}$ of the mod-$\ell$ reduction `reductionModL A p x`.
--
--   This is the good-reduction (Néron) model of the Jacobian of $X_0(p)$ over $\mathbf{Z}_{(\ell)}$ for $\ell \nmid p$, packaged together with the two identifications that make it usable: $\mathrm{Pic}^0$ of the curve over $\overline{\mathbf{Q}}$ as the generic-fibre points, Galois-equivariantly, and $\mathrm{Pic}^0$ over the residue field at a place above $\ell$ as the special-fibre points, compatibly with reduction of points. It is the input for the finite flat models of the torsion of $J_0(p)$ and for the surjectivity of reduction on torsion away from $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jZero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_abelianSchemePropertyBundle_model_jZero
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p) :
    ∃ (J : Scheme.{0})
      (f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
      (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f),
      AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
        (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) ∧
      (∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ → ReductionInputsModL A p →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) f)
          (ptsSp : JZeroC (ResidueField ↥A) p ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f),
          (∀ x : JZero p, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v)) ∧
          ReductionOfPointsAgreesModL p A f σA ptsA ptsSp) := by sorry
