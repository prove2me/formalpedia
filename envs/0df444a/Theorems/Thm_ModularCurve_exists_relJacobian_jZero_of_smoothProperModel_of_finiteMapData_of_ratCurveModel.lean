-- Prove2me | Theorems.Thm_ModularCurve_exists_relJacobian_jZero_of_smoothProperModel_of_finiteMapData_of_ratCurveModel
-- name    : ModularCurve.exists_relJacobian_jZero_of_smoothProperModel_of_finiteMapData_of_ratCurveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/b2e9c012-162d-5ccd-8b7b-785681d0d7d6
-- title:
--   Relative Jacobian of X₀(p) over ℤ_{(ℓ)} from finite-map data
-- statement:
--   Fix $p\neq 0$ and a prime $\ell$ with $\ell\nmid p$, and write $R=\mathbf{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of rationals whose denominator is coprime to $\ell$. Let $c\colon X\to\operatorname{Spec}R$ be proper, smooth of relative dimension $1$ and geometrically integral, with a section $\varepsilon$, and assume that for every $m_0$ there is a `SmoothProperCurve.FiniteMapData` for $(c,\varepsilon)$ of degree $m\ge m_0$ whose level sets are generically étale: two affine opens $U=X\smallsetminus\varepsilon$, $V$ covering $X$ with $U\cap V=D(f)=D(g)$ and $fg=1$ there, $\Gamma(X,U)$ finite over $R[f]$ and $\Gamma(X,V)$ finite over $R[g]$, all level sets $S\otimes_R\Gamma(X,U)/(1\otimes f-s\otimes 1)$ finite free of rank $m$ over local $R$-algebras $S$, and étale whenever $D(s)$ is a unit for a fixed polynomial $D$ with a unit coefficient. Further data are assumed: a smooth proper model $M_\eta$ over $\overline{\mathbf{Q}}$ of the function field `modularFunctionFieldBar p` (a `CurveModel`: an integral proper smooth relative curve with prescribed function field and a bijection between closed points and places matching stalks with valuation subrings), together with an isomorphism $e_\eta$ onto the geometric generic fibre of $c$ compatible with the base maps and Galois-equivariant on places via `arithmeticGalois`; a `CurveModel` $M_0$ over $\mathbf{Q}$ of `modularFunctionFieldFull p` with an isomorphism $e_0$ onto the $\mathbf{Q}$-fibre, the places of $M_\eta$ restricting along the base-change embedding $\overline{\mathbf{Q}}\otimes_{\mathbf{Q}}$ to those of $M_0$; for every valuation subring $A\subset\overline{\mathbf{Q}}$ with $\ell\in A$ non-unit, a ring map $\rho_A\colon R\to A$ lifting $R\to\overline{\mathbf{Q}}$, a `CurveModel` $M_A$ over the residue field of $A$ of `modularFunctionFieldFullC` and an isomorphism onto the fibre of $c$ along $\mathrm{residue}\circ\rho_A$; and, when that residue field is algebraically closed, a place-reduction map $r$ satisfying `IsPlaceReductionModL` under which specialisation of points of $X$ from $\overline{\mathbf{Q}}$ to the residue field matches $r$ on the associated places. Then, with `JZero p` the degree-zero Picard group of `modularFunctionFieldBar p` over $\overline{\mathbf{Q}}$ carrying the Hecke-module structure `heckeModuleBar p`, there exist a scheme $J$, a morphism $f\colon J\to\operatorname{Spec}R$, a relative group law $L$ on $f$, and a bijection $\mathrm{pts}$ from `JZero p` to the sections of $f$ over $\operatorname{Spec}\overline{\mathbf{Q}}$ such that: $f$ is smooth, proper, with connected fibres and admits a relative group law (`AbelianSchemePropertyBundle`); $L$ is commutative on $T$-points for all $T$; $\mathrm{pts}$ is additive; $\mathrm{pts}(\sigma\cdot x)$ is $\operatorname{Spec}\sigma$ followed by $\mathrm{pts}(x)$ for every $\sigma\in\operatorname{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$; for every $A$ over $\ell$ there are a morphism $\sigma_A\colon\operatorname{Spec}A\to\operatorname{Spec}R$ and bijections $\mathrm{pts}_A$ on `JZero p` and $\mathrm{pts}_{\mathrm{sp}}$ on `JZeroC (ResidueField A) p` onto the $A$- and residue-field-points of $f$ over $\sigma_A$, with $\mathrm{pts}_A$ agreeing with $\mathrm{pts}$ on underlying morphisms, $\mathrm{pts}_{\mathrm{sp}}$ additive, and `ReductionOfPointsAgreesModL` holding whenever `ReductionInputsModL A p` does; and every $t$ in `HeckeAlg` $=\mathrm{MvPolynomial}\,\mathrm{Nat.Primes}\,\mathbf{Z}$ is realised by an endomorphism $\varphi$ of $f$ over the base which is additive for $L$ and satisfies $\mathrm{pts}(t\cdot x)=\mathrm{pts}(x)$ followed by $\varphi$.
--
--   This is the construction, over $\mathbf{Z}_{(\ell)}$ with $\ell\nmid p$, of the relative Jacobian of a smooth proper model of $X_0(p)$ as an abelian scheme with commutative group law, Galois-equivariant parametrisation of its $\overline{\mathbf{Q}}$-points by $\mathrm{Pic}^0$ of the modular function field, compatible reduction of points modulo $\ell$, and Hecke endomorphisms. It is the edition whose input is finite-map chart data together with an explicit $\mathbf{Q}$-model of the generic fibre, and it feeds [`ModularCurve.exists_relJacobian_jZero`](thm.html#ModularCurve.exists_relJacobian_jZero), the good-reduction Jacobian used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_relJacobian_jZero_of_smoothProperModel_of_finiteMapData_of_ratCurveModel.lean

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
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_relJacobian_jZero_of_smoothProperModel_of_finiteMapData_of_ratCurveModel
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)

    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull p))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))

    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → (↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p),
        IsPlaceReductionModL A p r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x)) :
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
