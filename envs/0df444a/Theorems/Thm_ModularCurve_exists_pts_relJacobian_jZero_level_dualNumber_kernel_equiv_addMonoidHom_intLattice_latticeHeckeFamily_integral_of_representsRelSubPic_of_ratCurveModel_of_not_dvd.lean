-- Prove2me | Theorems.Thm_ModularCurve_exists_pts_relJacobian_jZero_level_dualNumber_kernel_equiv_addMonoidHom_intLattice_latticeHeckeFamily_integral_of_representsRelSubPic_of_ratCurveModel_of_not_dvd
-- name    : ModularCurve.exists_pts_relJacobian_jZero_level_dualNumber_kernel_equiv_addMonoidHom_intLattice_latticeHeckeFamily_integral_of_representsRelSubPic_of_ratCurveModel_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/70a73140-de1d-5923-b09c-b02ab155ac74
-- title:
--   Tangent space of the relative Jacobian of X₀(N) at p
-- statement:
--   Throughout, $R$ denotes the subring $\mathrm{ratLocalizedAt}\ p$ of $\mathbf{Q}$ consisting of those rationals whose denominator is coprime to $p$, i.e. $\mathbf{Z}_{(p)}$.
--
--   Fixed data: a non-zero natural number $N$, a prime $p$ with $p \nmid N$, a scheme $X$ (in universe $0$) together with a morphism $c : X \to \operatorname{Spec} R$ that is proper, smooth of relative dimension $1$ and geometrically integral, and a section $\varepsilon$ of $c$, that is, an element of `SchemeHomOver (𝟙 (Spec R)) c`: a morphism $\operatorname{Spec} R \to X$ whose composite with $c$ is the identity.
--
--   Chart hypothesis `h𝔉`: for every $m_0$ there is a `SmoothProperCurve.FiniteMapData` $\mathfrak{F}$ for $(c,\varepsilon)$ with $m_0 \le \mathfrak{F}.m$ and satisfying $\mathfrak{F}.\mathrm{LevelSetsGenericallyEtale}$. Such data consist of two affine opens $U, V$ of $X$ with $U \sqcup V = \top$, sections $f \in \Gamma(X,U)$, $g \in \Gamma(X,V)$ and a natural number $m$, such that $U$ is exactly the complement of the image of $\varepsilon$, $U \cap V$ equals both the basic open set of $f$ and that of $g$, the restrictions of $f$ and $g$ to $U \cap V$ are mutually inverse, $\Gamma(X,U)$ is finite over $R[T]$ via $T \mapsto f$ and $\Gamma(X,V)$ is finite over $R[T]$ via $T \mapsto g$, and for every local $R$-algebra $S$ and every $s \in S$ the level set $S \otimes_R \Gamma(X,U)/(1 \otimes f - s \otimes 1)$ is a finite free $S$-module of rank $m$; the predicate `LevelSetsGenericallyEtale` asserts the existence of a polynomial $D \in R[T]$ one of whose coefficients is a unit, such that for every local $R$-algebra $S$ with local structure map and every $s \in S$ with $D(s)$ a unit, that level-set algebra is étale over $S$.
--
--   Geometric generic fibre, `Mη`, `eη`, `heη`, `hgal`: a curve model $M_\eta$ over $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` of the function field `modularFunctionFieldBar N` (the base change to $\overline{\mathbf{Q}}$, inside Laurent series, of the modular function field `modularFunctionFieldFull N`), an isomorphism $e_\eta$ from $M_\eta.C$ onto the pullback of $c$ along $\operatorname{Spec}$ of $R \to \overline{\mathbf{Q}}$, with $e_\eta$ followed by the second projection equal to $M_\eta.\mathrm{toBase}$, and the equivariance hypothesis `hgal`: for $g \in \operatorname{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ and $\overline{\mathbf{Q}}$-points $x, x'$ of $M_\eta.C$ over the base, if $x'$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by the same composite for $x$, then $M_\eta.\mathrm{pointEquivPlace}\ x'$ is the image of $M_\eta.\mathrm{pointEquivPlace}\ x$ under the action of the semilinear automorphism $\mathrm{arithmeticGalois}\ g$ on places.
--
--   Places above $p$, `ρ`, `hρ`: for every valuation subring $A$ of $\overline{\mathbf{Q}}$ with $A.\mathrm{LiesOverPrime}\ p$ (i.e. $p$ lies in the non-units of $A$) a ring homomorphism $\rho_A : R \to A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbf{Q}}$ is the structure map $R \to \overline{\mathbf{Q}}$.
--
--   Special fibres, `Ms`, `es`, `hes_iso`, `hes`: for each such $A$ a curve model $M_{s,A}$ over the residue field $\kappa_A$ of $A$ of the field `modularFunctionFieldFullC κ_A N`, together with a morphism $e_{s,A}$ from $M_{s,A}.C$ to the pullback of $c$ along $\operatorname{Spec}$ of the residue map composed with $\rho_A$, which is an isomorphism and satisfies $e_{s,A}$ followed by the second projection $= M_{s,A}.\mathrm{toBase}$.
--
--   Reduction of places, `hsp`: for each $A$ over $p$ with algebraically closed residue field there is a map $r$ from places of `modularFunctionFieldBar N` over $\overline{\mathbf{Q}}$ to places of `modularFunctionFieldFullC κ_A N` over $\kappa_A$ satisfying `IsPlaceReductionModL A N r`, and such that for every $A$-point $x_A$ of $X$ over $\operatorname{Spec}(\rho_A)$, every $\overline{\mathbf{Q}}$-point $x$ of $M_\eta.C$ and every $\kappa_A$-point $y$ of $M_{s,A}.C$ over their bases, if $x$ followed by $e_\eta$ and the first projection is $\operatorname{Spec}$ of $A \hookrightarrow \overline{\mathbf{Q}}$ followed by $x_A$, and $y$ followed by $e_{s,A}$ and the first projection is $\operatorname{Spec}$ of the residue map followed by $x_A$, then $M_{s,A}.\mathrm{pointEquivPlace}\ y = r(M_\eta.\mathrm{pointEquivPlace}\ x)$.
--
--   Rational model, `M₀`, `e₀`, `he₀`, `hcompat`: a curve model $M_0$ over $\mathbf{Q}$ of `modularFunctionFieldFull N`, an isomorphism $e_0$ from $M_0.C$ onto the pullback of $c$ along $\operatorname{Spec}$ of $R \to \mathbf{Q}$ with $e_0$ followed by the second projection $= M_0.\mathrm{toBase}$, and `hcompat`: for every $\overline{\mathbf{Q}}$-point $x$ of $M_\eta.C$ over the base, every $\overline{\mathbf{Q}}$-point $y$ of that pullback and every closed point $x_0$ of $M_0.C$, if $y$ followed by the first projection equals $x$ followed by $e_\eta$ and the first projection, and if the base map of $y$ followed by $e_0^{-1}$ sends the closed point of $\overline{\mathbf{Q}}$ to $x_0$, then the preimage of the valuation subring of $M_\eta.\mathrm{pointEquivPlace}\ x$ under the ring map $\mathrm{modularFunctionFieldFull}\ N \to \mathrm{modularFunctionFieldBar}\ N$ given by inclusion into the right factor of $\overline{\mathbf{Q}} \otimes_{\mathbf{Q}} \mathrm{modularFunctionFieldFull}\ N$ followed by `baseChangeEquiv` coincides with the valuation subring of $M_0.\mathrm{placeOfPoint}\ x_0$.
--
--   Picard data, `D`, `hD`, `hsm`, `hpr`, `hgc`: a `RelativePic0Designation` $D$ for $c$ over $R$, i.e. a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R$ and a zero section; the hypothesis `hD` that $D$ represents the relative rigidified Picard functor of $(c,\varepsilon)$ cut out by `algEquivZeroCut c ε`, the condition that a rigidified line bundle be fibrewise algebraically equivalent to zero over every algebraically closed field point of the base (a Poincaré bundle satisfying that condition, the universal property that every such rigidified bundle over a base $t$ is induced by a unique $t$-point of $D.\mathrm{toBase}$, and triviality of the pullback along the zero section); and the hypotheses that $D.\mathrm{toBase}$ is smooth, proper and geometrically connected.
--
--   In the conclusion, `JZero N` (the group $\mathrm{Pic}^0$ of degree-zero divisor classes of `modularFunctionFieldBar N` over $\overline{\mathbf{Q}}$) carries the `HeckeAlg`-module structure `heckeModuleBar N`, where $\mathrm{HeckeAlg} = \mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbf{Z}$ (this structure is given by the Hecke evaluation map when the Hecke operators on `JZero N` commute, and by the zero evaluation otherwise), and the lattice $\mathrm{intLattice}\ N\ 2$, the $\mathbf{Z}$-span in $S_2(\Gamma_0(N))$ of the cusp forms all of whose $q$-expansion coefficients are integers, carries the `HeckeAlg`-module structure coming from the commuting family `latticeHeckeFamily N`, in which the variable at a prime $\ell$ acts by $U_\ell$ if $\ell \mid N$ and by $T_\ell$ otherwise.
--
--   Assertion: there exist a bijection $\mathrm{pts}$ from `JZero N` onto the $\overline{\mathbf{Q}}$-points of $D.\mathrm{toBase}$, i.e. `SchemeHomOver (Spec.map (R → AlgebraicClosure ℚ)) D.toBase`, and a map $\varphi$ from $\mathrm{HeckeAlg}$ to `SchemeHomOver D.toBase D.toBase`, that is, to endomorphisms of $D.P$ over $\operatorname{Spec} R$, such that the following hold, where $L$ denotes the relative group law `RepresentsRelSubPic.relativeGroupLaw` attached to `hD` for the group cut `algEquivZeroGroupCut c ε`.
--
--   (i) `AbelianSchemePropertyBundle R D.toBase`: $D.\mathrm{toBase}$ is smooth and proper, each fibre $D.\mathrm{toBase}^{-1}(s)$ over a point $s$ of $\operatorname{Spec} R$ is connected, and a relative group law on $D.\mathrm{toBase}$ over $R$ exists.
--
--   (ii) $L$ is commutative: for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ of $D.\mathrm{toBase}$ over $t$, $L.\mathrm{mul}\ t\ x\ y = L.\mathrm{mul}\ t\ y\ x$.
--
--   (iii) $\mathrm{pts}$ is additive: $\mathrm{pts}(x+y) = L.\mathrm{mul}\ (\mathrm{pts}\ x)\ (\mathrm{pts}\ y)$ for all $x, y$ in `JZero N`.
--
--   (iv) $\mathrm{pts}$ is Galois-equivariant: for $\sigma \in \operatorname{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ and $x$ in `JZero N`, the underlying morphism of $\mathrm{pts}(\sigma \cdot x)$ equals $\operatorname{Spec}(\sigma)$ followed by the underlying morphism of $\mathrm{pts}\ x$.
--
--   (v) For every valuation subring $A$ of $\overline{\mathbf{Q}}$ lying over $p$ there exist a morphism $\sigma_A : \operatorname{Spec} A \to \operatorname{Spec} R$, a bijection $\mathrm{pts}_A$ from `JZero N` onto the points of $D.\mathrm{toBase}$ over $\operatorname{Spec}(A \hookrightarrow \overline{\mathbf{Q}})$ followed by $\sigma_A$, and a bijection $\mathrm{pts}_{\mathrm{Sp}}$ from `JZeroC κ_A N` (degree-zero divisor classes of `modularFunctionFieldFullC κ_A N` over $\kappa_A$) onto the points of $D.\mathrm{toBase}$ over $\operatorname{Spec}$ of the residue map followed by $\sigma_A$, such that the underlying morphism of $\mathrm{pts}_A\ x$ equals that of $\mathrm{pts}\ x$ for every $x$, $\mathrm{pts}_{\mathrm{Sp}}$ is additive for $L$, and, under the hypothesis `ReductionInputsModL A N`, `ReductionOfPointsAgreesModL N A D.toBase σA ptsA ptsSp` holds: every $x$ in `JZero N` has an $A$-valued point $x_A$ of $D.\mathrm{toBase}$ over $\sigma_A$ whose composite with $\operatorname{Spec}(A \hookrightarrow \overline{\mathbf{Q}})$ is $\mathrm{pts}_A\ x$ and whose composite with $\operatorname{Spec}$ of the residue map is $\mathrm{pts}_{\mathrm{Sp}}$ of the reduction of $x$ modulo $A$.
--
--   (vi) For every $t \in \mathrm{HeckeAlg}$: the endomorphism $\varphi\ t$ is a homomorphism for $L$, in the sense that for every $T$, every $s : T \to \operatorname{Spec} R$ and all $x, y$ over $s$, the composite of $L.\mathrm{mul}\ s\ x\ y$ with $\varphi\ t$ equals $L.\mathrm{mul}\ s$ applied to the composites of $x$ and of $y$ with $\varphi\ t$; and $\mathrm{pts}$ intertwines the Hecke action with $\varphi$: the underlying morphism of $\mathrm{pts}(t \cdot x)$ is that of $\mathrm{pts}\ x$ followed by $\varphi\ t$, for all $x$ in `JZero N`.
--
--   (vii) There exists a bijection $\tau$ from the set $K$ of those points of $D.\mathrm{toBase}$ over $\operatorname{Spec}$ of $R \to R[\epsilon]$ (with $R[\epsilon] = \mathrm{DualNumber}\ R$) whose composite with $\operatorname{Spec}$ of the projection $R[\epsilon] \to R$ is the identity section $L.\mathrm{one}$ at $\operatorname{Spec}$ of $\mathrm{algebraMap}\ R\ R$, onto the group $\mathrm{Hom}_{+}(\mathrm{intLattice}\ N\ 2,\ R)$ of additive maps from the integral weight-two cusp-form lattice to $R$, such that: $\tau$ is additive, i.e. for $x, y, z \in K$ with the underlying point of $z$ equal to $L.\mathrm{mul}$ of those of $x$ and $y$ one has $\tau z = \tau x + \tau y$; and $\tau$ is Hecke-adjoint, i.e. for every $t \in \mathrm{HeckeAlg}$ and $x, y \in K$ whose underlying morphisms satisfy $y = x$ followed by $\varphi\ t$, one has $\tau y\ g = \tau x\ (t \cdot g)$ for every $g \in \mathrm{intLattice}\ N\ 2$.
--
--   This is the integral tangent-space package for the Jacobian of $X_0(N)$ at a prime $p$ of good reduction: the representing scheme of $\mathrm{Pic}^0$ is an abelian scheme over $\mathbf{Z}_{(p)}$ with commutative group law, its $\overline{\mathbf{Q}}$-points are identified Galois- and Hecke-equivariantly with $J_0(N)(\overline{\mathbf{Q}})$ compatibly with reduction at places above $p$, and the kernel of reduction on dual-number points (the Lie algebra) is identified, Hecke-adjointly, with the $\mathbf{Z}_{(p)}$-valued additive dual of the lattice of weight-two cusp forms with integral $q$-expansions. It is used by [`ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq`](thm.html#ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pts_relJacobian_jZero_level_dualNumber_kernel_equiv_addMonoidHom_intLattice_latticeHeckeFamily_integral_of_representsRelSubPic_of_ratCurveModel_of_not_dvd.lean

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
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_LatticeHeckeFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing CuspForm

open AlgebraicGeometry.RelPicard
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_pts_relJacobian_jZero_level_dualNumber_kernel_equiv_addMonoidHom_intLattice_latticeHeckeFamily_integral_of_representsRelSubPic_of_ratCurveModel_of_not_dvd
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)

    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)

    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))

    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt p) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    :
    letI := heckeModuleBar N
    letI := (CuspForm.latticeHeckeFamily N).module
    ∃ (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) D.toBase)
      (φ : HeckeAlg → SchemeHomOver D.toBase D.toBase),
      AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt p) D.toBase ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
        (x y : SchemeHomOver t D.toBase), (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul t x y = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul t y x) ∧
      (∀ x y : JZero N, pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero N),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
          (ptsA : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) D.toBase)
          (ptsSp : JZeroC (ResidueField ↥A) N ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) D.toBase),
          (∀ x : JZero N, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JZeroC (ResidueField ↥A) N, ptsSp (u + v) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (ptsSp u) (ptsSp v)) ∧
          (ReductionInputsModL A N → ReductionOfPointsAgreesModL N A D.toBase σA ptsA ptsSp)) ∧
      (∀ t : HeckeAlg,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (x y : SchemeHomOver s D.toBase),
          NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul s x y) (φ t) =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul s (NeronModelInfra.schemeHomOverComp x (φ t))
              (NeronModelInfra.schemeHomOverComp y (φ t))) ∧
        ∀ x : JZero N, (pts (t • x)).1 = (pts x).1 ≫ (φ t).1) ∧
      ∃ τ : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (Spec.map (CommRingCat.ofHom
                (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1} ≃
          (↥(CuspForm.intLattice N 2) →+ ↥(GaloisRep.ratLocalizedAt p)),
        (∀ x y z : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (Spec.map (CommRingCat.ofHom
                (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1},
          z.1 = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x.1 y.1 → τ z = τ x + τ y) ∧
        ∀ (t : HeckeAlg) (x y : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (Spec.map (CommRingCat.ofHom
                (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1}),
          y.1.1 = x.1.1 ≫ (φ t).1 →
            ∀ g : ↥(CuspForm.intLattice N 2),
              τ y g = τ x (t • g) := by sorry
