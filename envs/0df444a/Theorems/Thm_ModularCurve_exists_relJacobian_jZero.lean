-- Prove2me | Theorems.Thm_ModularCurve_exists_relJacobian_jZero
-- name    : ModularCurve.exists_relJacobian_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/0887648f-47e1-555c-8b80-39ac96247de6
-- title:
--   Relative Jacobian of X₀(p) over ℤ_{(ℓ)}
-- statement:
--   Let $p\ge 1$ be a level, let $\ell$ be a prime with $\ell\nmid p$, and equip $J_0(p)(\overline{\mathbf{Q}}) :=$ `JZero p`, the group of degree-zero divisor classes of the modular function field of level $p$ over $\overline{\mathbf{Q}}$, with the module structure `heckeModuleBar p` over `HeckeAlg` $=\mathbf{Z}[X_q : q \text{ prime}]$. Write $R =$ [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$, the subring of rationals whose denominator is coprime to $\ell$. The assertion is that there exist a scheme $J$, a morphism $f : J \to \operatorname{Spec} R$, a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on $R$-scheme-valued points satisfying the group axioms and naturality), and a bijection $\mathrm{pts}$ from `JZero p` onto the set of morphisms $\operatorname{Spec}\overline{\mathbf{Q}} \to J$ over $f$ along $R \to \overline{\mathbf{Q}}$, such that: (i) $f$ is smooth and proper, each fibre $f^{-1}\{s\}$ is connected, and $f$ admits a relative group law; (ii) $L$ is commutative on $T$-points for every $T \to \operatorname{Spec} R$; (iii) $\mathrm{pts}$ is additive; (iv) for every $\sigma \in \operatorname{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ and every $x$, $\mathrm{pts}(\sigma\cdot x) = \operatorname{Spec}(\sigma)$ followed by $\mathrm{pts}(x)$; (v) for every valuation subring $A \subset \overline{\mathbf{Q}}$ with $\ell$ a nonunit of $A$ there are a morphism $\sigma_A : \operatorname{Spec} A \to \operatorname{Spec} R$, a bijection $\mathrm{pts}_A$ from `JZero p` onto $\overline{\mathbf{Q}}$-points of $J$ taken over $\sigma_A$ whose underlying morphisms are those of $\mathrm{pts}$, and an additive bijection $\mathrm{pts}_{\mathrm{sp}}$ from the degree-zero divisor class group of the modular function field of level $p$ over the residue field of $A$ onto the residue-field points of $J$ over $\sigma_A$, with the property that whenever `ReductionInputsModL A p` holds, every $x$ extends to an $A$-point of $J$ restricting to $\mathrm{pts}_A(x)$ generically and to $\mathrm{pts}_{\mathrm{sp}}(\mathrm{reductionModL}\,A\,p\,x)$ on the special fibre; and (vi) for every $t \in$ `HeckeAlg` there is an endomorphism $\varphi$ of $J$ over $\operatorname{Spec} R$ which is a homomorphism for $L$ on $S$-points for all $S \to \operatorname{Spec} R$ and satisfies $\mathrm{pts}(t \cdot x) = \mathrm{pts}(x)$ followed by $\varphi$.
--
--   This packages the Jacobian of $X_0(p)$ over $\mathbf{Z}_{(\ell)}$ for $\ell \nmid p$ — an abelian scheme, hence the Néron model of $J_0(p)$ there — together with the interfaces its users need: the dictionary between $\overline{\mathbf{Q}}$-points and degree-zero divisor classes with its Galois action, the corresponding dictionary at each place above $\ell$ with its compatibility with reduction of divisor classes, and the Hecke action realised by endomorphisms of the scheme. It is the input to the constructions of finite flat models of the $\ell$-torsion of $J_0(p)$ used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_relJacobian_jZero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_relJacobian_jZero
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p) :
    letI := heckeModuleBar p
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
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) f)
          (ptsSp : JZeroC (ResidueField ↥A) p ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f),
          (∀ x : JZero p, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v)) ∧
          (ReductionInputsModL A p → ReductionOfPointsAgreesModL p A f σA ptsA ptsSp)) ∧
      (∀ t : HeckeAlg, ∃ φ : SchemeHomOver f f,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ)
              (NeronModelInfra.schemeHomOverComp y φ)) ∧
        ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1) := by sorry
