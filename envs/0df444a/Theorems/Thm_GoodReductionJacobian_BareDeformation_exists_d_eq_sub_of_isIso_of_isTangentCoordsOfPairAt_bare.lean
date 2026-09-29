-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3a6a0403-d1d9-5e79-9835-734fec6c4c07
-- title:
--   Isomorphic regluings have cohomologous tangent cocycles
-- statement:
--   Setting. Let $B$ be an artinian local ring whose residue field $k=\mathrm{ResidueField}\,B$ is algebraically closed, and let $B_1$ be a commutative $B$-algebra. Three hypotheses describe the extension: `hπ` says that $\mathrm{algebraMap}\,B\,B_1$ is surjective, `hker` that its kernel $I$ is a nilpotent ideal, and `hsmall` that $I\cdot\mathfrak m_B=0$; `hI` adds $I\le\mathfrak m_B$. Over $B_1$ there is given a morphism $f_1:A_1\to\operatorname{Spec} B_1$ together with a relative group law $L_1$ on it (a functorial group structure on the $T$-points of $f_1$ over $\operatorname{Spec} B_1$, natural in $T$), the hypothesis `hc₁` that $L_1$ is commutative, and the hypothesis `h₁` that the bundle `AbelianSchemePropertyBundle B₁ f₁` holds, i.e. $f_1$ is smooth and proper, all its fibres are connected, and $f_1$ admits a relative group law.
--
--   The tangent module. $V$ is a finite-dimensional $k$-vector space, carrying in addition a $B$-module structure compatible with the $k$-structure through the scalar tower $B\to k$ and a right $k$-action with central scalars; $\iota:V\to B$ is $B$-linear, `hι` asserts that it is injective and `hιI` that its range, viewed as a $B$-submodule, is exactly the kernel $I$ of $\mathrm{algebraMap}\,B\,B_1$. Thus $V$ identifies with $I$ as a $B$-module.
--
--   The base deformation and its cover. $D_0$ is a bare deformation of $(f_1,L_1)$ to $B$, that is: a scheme $D_0.A$ with a morphism $D_0.f:D_0.A\to\operatorname{Spec} B$, a commutative relative group law $D_0.L$ on $D_0.f$, the abelian-scheme property bundle for $D_0.f$, and a morphism $D_0.g:A_1\to D_0.A$ making $(D_0.g,f_1,D_0.f,\operatorname{Spec}(B\to B_1))$ a pullback square and compatible with the multiplication maps of $L_1$ and $D_0.L$. The morphism $D_0.f$ is assumed separated. $\mathcal U$ is an ordered affine cover of $D_0.A$: a finite linearly ordered index set $\mathcal U.\iota$, affine opens $\mathcal U.U\,i$ with supremum $\top$; for a strictly monotone $s:\mathrm{Fin}(i+1)\to\mathcal U.\iota$ the open $\mathcal U.\mathrm{inter}\,s$ is the intersection of the corresponding charts. A distinguished index $i_0$ is given, with $e_0:\operatorname{Spec} B\to\mathcal U.U\,i_0$ such that $e_0$ followed by the open immersion of $\mathcal U.U\,i_0$ is the unit section of $D_0.L$ over $\mathrm{id}_{\operatorname{Spec} B}$ (`he₀`), and, on the base change of $D_0.f$ along $\operatorname{Spec} k\to\operatorname{Spec} B$, a morphism $e_1:\operatorname{Spec} k\to(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$ such that $e_1$ followed by the open immersion is the unit section of the base-changed group law (`he₁`). Here the base-changed cover is the preimage cover of the pullback $\operatorname{pullback}\,D_0.f\,(\operatorname{Spec}(B\to k))$ under its first projection.
--
--   Comparison of sections. For every overlap index $s\in\mathcal U.\mathrm{Idx}\,1$ a ring isomorphism $\sigma_s: k\otimes_B\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)\to\Gamma(\text{pullback},(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).\mathrm{inter}\,s)$ is given, with `hσ₁` stating that $\sigma_s(1\otimes x)$ is the restriction of the pullback of $x$ along the first projection, and `hσ₂` that $\sigma_s(a\otimes 1)$ is the image of $a\in k$ under the structure map of the $k$-algebra of sections.
--
--   The two cocycles. Let $\mathcal O$ denote the $\mathcal O$-module presheaf `OModulePresheaf.unit` of the second projection, whose sections on an open are the sections of the structure sheaf of the pullback; its $i$-cochains on the base-changed cover are the families indexed by $\mathcal U.\mathrm{Idx}\,i$ of sections over the corresponding intersections, with Čech differentials `d`. Two elements $c,c'$ are given of $\mathrm{PointDerivations}$ of the $k$-algebra $\Gamma(\text{pullback},(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0)$ at the evaluation homomorphism determined by $e_1$ (through the top isomorphism of the chart and the $\Gamma$–$\operatorname{Spec}$ isomorphism), with values in the $k$-space of $k$-linear maps $\mathrm{Hom}_k(V,k)\to(\text{$1$-cochains})$; that is, $c$ and $c'$ are $k$-linear maps $D$ on that algebra satisfying $D(ab)=\mathrm{ev}(a)\,D(b)+\mathrm{ev}(b)\,D(a)$. The hypotheses `hc` and `hc'` state that for every section $a$ and every $\xi\in V^{\vee}$ the $1$-cochains $c\,a\,\xi$ and $c'\,a\,\xi$ lie in the kernel of the Čech differential in degree $1$, i.e. are cocycles.
--
--   The regluings. $\tau,\tau'$ are families of automorphisms of each overlap $\mathcal U.\mathrm{inter}\,s$ (as schemes), and $D,D'$ are bare deformations of $(f_1,L_1)$ to $B$ with `hD`: $D_0.\mathrm{IsRegluingBy}\,\mathcal U\,\tau\,D$ and `hD'`: $D_0.\mathrm{IsRegluingBy}\,\mathcal U\,\tau'\,D'$. The predicate $\mathrm{IsRegluingBy}$ requires: each $\tau_s$ is a morphism over $\operatorname{Spec} B$ (composing $\tau_s$ with the inclusion and $D_0.f$ gives the inclusion followed by $D_0.f$); each $\tau_s$ is the identity on the part coming from $A_1$ (the restriction of $D_0.g$ to the overlap, followed by $\tau_s$, equals that restriction); and there exist morphisms $\iota_i:\mathcal U.U\,i\to D.A$ which are open immersions, are morphisms over $\operatorname{Spec} B$, have images covering all points of $D.A$, are compatible with $D_0.g$ and $D.g$, and satisfy the gluing identity: on each overlap $s$, the inclusion into the smaller-index chart followed by $\iota_{s(0)}$ equals $\tau_s$ followed by the inclusion into the larger-index chart followed by $\iota_{s(1)}$.
--
--   Coordinates of the regluing data. The hypothesis `hτ` states that for every overlap index $s$ there exists a family $c_s$ of $k$-linear maps $V^{\vee}\to k\otimes_B\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$, indexed by the sections over the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$, such that [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) holds for the data $I$, $V$, $\iota$, the ring $\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$, the pair of $\operatorname{Spec}$-points consisting of the canonical map `fromSpec` of the affine overlap and of the map $\mathrm{isoSpec}^{-1}$ followed by $\tau_s$ followed by the open immersion, the second projection of the pullback with its base-changed group law, the first projection, and the chart $U\,i_0$; unfolded, this asserts the existence of a point $w_0$ of the base-changed scheme with values in the thickening $\operatorname{Spec}(k\otimes_B C)\otimes_k(k\oplus V)$ lying over the canonical base morphism, and of a lift $w_1$ into the chart, such that $w_0$ followed by the first projection is a tangent vector of the given pair in the sense of `IsTangentOfPair` (it factors, via a Schlessinger map out of the pair ring of $I$ and $C$, through a morphism restricting to the two given points along the two projections of the pair ring), such that $w_1$ followed by the inclusion of the chart is the translate of $w_0$ to the unit section by the base-changed group law, and such that $c_s$ is the tangent-coordinate family `tangentCoords` of the ring homomorphism $\Gamma\to$ thickening induced by $w_1$. In addition `hτ` requires $\sigma_s(c_s\,a\,\xi)=(c\,a\,\xi)_s$ for all $a$ and all $\xi\in V^{\vee}$. The hypothesis `hτ'` is the same statement with $\tau'$ in place of $\tau$ and $c'$ in place of $c$.
--
--   Finally `hiso` asserts $D.\mathrm{IsIso}\,D'$, i.e. there is an isomorphism $e:D.A\cong D'.A$ with $e$ followed by $D'.f$ equal to $D.f$ and $D.g$ followed by $e$ equal to $D'.g$.
--
--   Conclusion. For every section $a$ of the structure sheaf of the pullback over the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$ and every $\xi\in\mathrm{Hom}_k(V,k)$ there exists a $0$-cochain $b$ of the presheaf `OModulePresheaf.unit` of the second projection on the base-changed cover whose Čech differential in degree $0$ equals $c\,a\,\xi-c'\,a\,\xi$. That is, the two $1$-cocycles attached to the regluing data $\tau$ and $\tau'$ differ by a coboundary, componentwise in $a$ and $\xi$.
--
--   This is the injectivity half of the dictionary between Čech $1$-cocycles of tangent coordinates on an ordered affine cover and isomorphism classes of bare deformations of an abelian scheme along a small extension $B\to B_1$: isomorphic regluings give cohomologous cocycles. It is used in the computation of the set of bare deformations over dual numbers for fake elliptic curves in the Čerednik–Drinfeld part of the development, and is deduced from the chart-automorphism comparison `exists_chartIso_comp_eq_of_isRegluingBy_of_isIso` together with `exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
    (c' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D D' : BareDeformation f₁ L₁ B)
    (hD : D₀.IsRegluingBy 𝒰 τ D) (hD' : D₀.IsRegluingBy 𝒰 τ' D')
    (hτ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)
    (hτ' : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ' s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)
    (hiso : D.IsIso D') :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 0,
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0 b =
          (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
          - (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ := by sorry
