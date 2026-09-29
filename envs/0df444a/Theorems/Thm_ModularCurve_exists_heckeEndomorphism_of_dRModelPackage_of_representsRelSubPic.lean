-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
-- name    : ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/e1d8d563-7df2-58bb-b6df-9cdf286b66c5
-- title:
--   Hecke endomorphisms of the integral model of J₀(p)
-- statement:
--   Let $p$ be a prime and let $\mathfrak{X}$ be a `DRModelPackage p`, i.e. a package of data for the two-chart integral model `DRModel p` of the modular curve of level $p$ over $\mathbb{Z}$ (properness, flatness and integrality of the model, normality on affine opens, a curve model over $\mathbb{Q}$ and one over $\overline{\mathbb{Q}}$ identified with the corresponding base changes together with their Galois and place compatibilities, two sections $\varepsilon_{\infty},\varepsilon_0$ of the structure morphism, and a distinguished smooth locus). Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}\colon D.P \to \operatorname{Spec}\mathbb{Z}$ and a section of it, and let $hD$ witness that $D$ represents the functor of line bundles on the model rigidified along $\varepsilon_{\infty}$ whose geometric fibres are algebraically equivalent to zero: a Poincaré rigidified bundle on the pullback along $D.\mathrm{toBase}$ satisfying that condition, universal for bundles satisfying it, with the zero section pulling back the Poincaré bundle to the unit. Write $L$ for the induced relative group law on $D.\mathrm{toBase}$ (functorial multiplication, unit and inverse on sections over $\operatorname{Spec}\mathbb{Z}$-schemes). Assume: $D.\mathrm{toBase}$ is smooth, separated, quasi-compact, geometrically connected and locally of finite type, and each of its point-fibres is preconnected; $L$ is commutative; multiplication by $n$ on $D.P$ is flat and surjective for every $n>0$; a bijection $\mathrm{pts}$ between $J_0(p) := \mathrm{Pic}^0$ of the modular function field over $\overline{\mathbb{Q}}$ and the $\overline{\mathbb{Q}}$-sections of $D.\mathrm{toBase}$, additive for $L$; a valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, such that for every $m$ prime to $p$ the $m$-torsion points of $J_0(p)$ whose associated $\overline{\mathbb{Q}}$-point factors through an $A$-point of $D.P$ are exactly `jZeroToricTorsion p A m`, the intersection of the $m$-torsion with the image of the inertia-invariant points under multiplication by the Eisenstein numerator; every point of $D.P$ over the residue field of $A$ lying over the induced map $\operatorname{Spec}$ of that residue field $\to \operatorname{Spec}\mathbb{Z}$ is annihilated by some $m>0$ prime to $p$, in the sense that composing it with multiplication by $m$ factors through the unit section; a general extension principle $hR1$ over discrete valuation rings $R$ with fraction field $K$ (for $G \to \operatorname{Spec} R$ with $G$ integral and the morphism locally of finite type, $H \to \operatorname{Spec} R$ separated, quasi-compact and locally of finite type, a closed-fibre point $\eta$ to which all closed-fibre points specialise and whose stalk is a discrete valuation ring, a morphism $\varphi_K$ of the $K$-fibres over $K$, and a subset of the closed fibre having $\eta$ in its closure each of whose points is reached by a local-domain point of $G \times_{\operatorname{Spec} R} H$ whose generic point lies in the image of the graph of $\varphi_K$, there is an open $V \subseteq G$ containing $\eta$ and all points outside the closed fibre and a morphism $V \to H$ over $\operatorname{Spec} R$ restricting to $\varphi_K$ on the $K$-fibre); hypothesis $hC1$, that for the Hecke module structure `heckeModuleBar p` on $J_0(p)$ and every $t$ in the Hecke algebra $\mathrm{MvPolynomial}\ \mathbb{N}\text{-primes}\ \mathbb{Z}$ there is an endomorphism $\varphi_{\eta}$ of the $\mathbb{Q}$-fibre of $D.\mathrm{toBase}$ over $\mathbb{Q}$, compatible with the base-changed group law and inducing $x \mapsto t \cdot x$ on $\overline{\mathbb{Q}}$-points via $\mathrm{pts}$; and hypothesis $hC2$, that for every prime $\ell$ not dividing $p$ every endomorphism of the $\mathbb{Q}$-fibre over $\mathbb{Q}$ extends to a morphism from the base change of $D.P$ along $\mathbb{Z} \to \mathbb{Z}_{(\ell)} = \{q \in \mathbb{Q} : \gcd(\mathrm{den}(q),\ell)=1\}$ to $D.P$, over the base and compatibly on the generic fibre. Then for every $t$ in the Hecke algebra there is a morphism $\varphi\colon D.P \to D.P$ over $\operatorname{Spec}\mathbb{Z}$ which is a homomorphism for $L$ (for all $T$, all $s\colon T \to \operatorname{Spec}\mathbb{Z}$ and all sections $x,y$ of $D.\mathrm{toBase}$ over $s$, composing $L$-product of $x$ and $y$ with $\varphi$ equals the $L$-product of the composites) and which realises $t$ on $\overline{\mathbb{Q}}$-points: $\mathrm{pts}(t \cdot x) = \mathrm{pts}(x)$ followed by $\varphi$ for all $x \in J_0(p)$.
--
--   This is the Hecke-action component of the Néron-type package for $J_0(p)$ over $\mathbb{Z}$: Hecke operators, given on the generic fibre and extended over $\mathbb{Z}_{(\ell)}$ for $\ell \neq p$ by the Néron property, are extended across the fibre at $p$ by the toric description of the integral torsion points and an extension principle over discrete valuation rings. It is used in the construction of the good identity component data for $J_0(p)$ by [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  AlgebraicGeometry.RelPicard

theorem ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)

    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hconn : GeometricallyConnected D.toBase)

    (hcomm : (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).IsCommutative)
    (hlft : LocallyOfFiniteType D.toBase)
    (hpre : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (D.toBase.base ⁻¹' {s}))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))

    (hnflat : ∀ n : ℕ, 0 < n → Flat
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul n))
    (hnsurj : ∀ n : ℕ, 0 < n → Surjective
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul n))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hvi : ∀ m : ℕ, ¬ p ∣ m →
      {x : JZero p | x ∈ jZeroTorsion p m ∧
          ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) D.toBase,
            (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1}
        = (jZeroToricTorsion p A m : Set (JZero p)))
    (hptors : ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ D.P,
      ζ ≫ D.toBase = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧
        ζ ≫ (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul m =
          ζ ≫ D.toBase ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).one (𝟙 _)).1)

    (hR1 : ∀ {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      {G H : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
      [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (η : G) (_hη : g.base η = IsLocalRing.closedPoint R)
      (_hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
      [IsDiscreteValuationRing (G.presheaf.stalk η)]
      (φK : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (hφK : φK ≫ pullback.snd h _ = pullback.snd g _)
      (Dset : Set G) (_hD : ∀ z ∈ Dset, g.base z = IsLocalRing.closedPoint R) (_hDη : η ∈ closure Dset)
      (_hpts : ∀ z ∈ Dset, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
      (c : Spec (CommRingCat.of A) ⟶ pullback g h),
      (c ≫ pullback.fst g h).base (IsLocalRing.closedPoint A) = z ∧
      c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
      (pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base),
      ∃ (V : G.Opens) (v : (V : Scheme.{0}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧ (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧ η ∈ V ∧
      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆ Set.range V.ι.base,
      IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
      φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))

    (hC1 : letI := heckeModuleBar p
      ∀ t : HeckeAlg,
      ∃ φη : SchemeHomOver
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
            (x y : SchemeHomOver s (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
          NeronModelInfra.schemeHomOverComp
              (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                  (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) ∧
        (∀ (x : JZero p)
            (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
          z ≫ pullback.fst D.toBase _ = (pts x).1 → zt ≫ pullback.fst D.toBase _ = (pts (t • x)).1 → zt = z ≫ φη.1))

    (hC2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ p →
      ∀ φη : SchemeHomOver
          (pullback.snd D.toBase (specGenericFibreInclusion ℤ ℚ))
          (pullback.snd D.toBase (specGenericFibreInclusion ℤ ℚ)),
      ∃ gA : pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ⟶ D.P,
        gA ≫ D.toBase = pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ≫ D.toBase ∧
        ∀ j : pullback D.toBase (specGenericFibreInclusion ℤ ℚ) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))),
          j ≫ pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) =
            pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ) →
          j ≫ gA = φη.1 ≫ pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ)) :

    letI := heckeModuleBar p
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by sorry
