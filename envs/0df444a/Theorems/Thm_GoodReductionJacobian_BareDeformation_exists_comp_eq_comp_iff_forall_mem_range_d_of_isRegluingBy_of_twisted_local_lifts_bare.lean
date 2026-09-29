-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_forall_mem_range_d_of_isRegluingBy_of_twisted_local_lifts_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_forall_mem_range_d_of_isRegluingBy_of_twisted_local_lifts_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a86c75bc-5d87-58e4-ac7d-6ed0bc9ee38d
-- title:
--   Coboundary criterion for lifting an endomorphism to a reglued deformation
-- statement:
--   Let $B$ be an artinian local ring with algebraically closed residue field $k=$ `ResidueField B`, and let $B_1$ be a $B$-algebra whose structure map is surjective with nilpotent kernel $I$, satisfying $I\cdot\mathfrak m_B=0$ and $I\subseteq\mathfrak m_B$. Let $f_1:A_1\to\operatorname{Spec}B_1$ carry a commutative relative group law $L_1$ and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, admitting a relative group law). Let $V$ be a finite-dimensional $k$-vector space which is also a $B$-module compatibly, with central right $k$-action, and let $\iota:V\to B$ be an injective $B$-linear map whose range is $I$ viewed as a $B$-submodule. Let $D_0$ be a bare deformation of $(f_1,L_1)$ over $B$: a scheme $D_0.A$ with $D_0.f:D_0.A\to\operatorname{Spec}B$, a commutative relative group law $D_0.L$, the abelian-scheme property bundle, and $D_0.g:A_1\to D_0.A$ making a cartesian square over $\operatorname{Spec}B_1\to\operatorname{Spec}B$ compatibly with the group laws; assume $D_0.f$ separated. Fix a finite ordered affine open cover $\mathcal U$ of $D_0.A$, an index $i_0$, and sections $e_0$, $e_1$ exhibiting the unit of $D_0.L$, respectively of its base change to $k$, as factoring through the chart $i_0$ of $\mathcal U$, respectively of the cover $\mathcal U$ base changed along $\operatorname{Spec}k\to\operatorname{Spec}B$; assume that this latter chart is affine. For each ordered pair $s$ of indices let $\sigma_s$ be a ring isomorphism $k\otimes_B\Gamma(D_0.A,\mathcal U_s)\cong\Gamma$ of the corresponding intersection in the base-changed cover, normalised so that $1\otimes x$ is the restriction of the pullback of $x$ along `pullback.fst` and $a\otimes 1$ is the image of $a$ under the structure map. Let $\tau_s$ be self-isomorphisms of the intersections $\mathcal U_s$ and let $D$ be a bare deformation with `D₀.IsRegluingBy 𝒰 τ D`: each $\tau_s$ commutes with $D_0.f$ and fixes the restriction of $D_0.g$, and $D.A$ is covered by the images of open immersions $\mathcal U_i\to D.A$ over $D_0.f$, compatible with $D_0.g$ and $D.g$, which on each overlap agree after insertion of $\tau_s$. Let $\varphi_1$ be an endomorphism of $A_1$ over $B_1$, and $j_\kappa$ a morphism from the fibre product $D_0.A\times_{\operatorname{Spec}B}\operatorname{Spec}k$ to $A_1$ with $j_\kappa$ followed by $D_0.g$ equal to the first projection. Let $mp_i:\mathcal U_i\to D.A$ be morphisms over $D_0.f$ which on the closed fibre compute $\varphi_1$ followed by $D.g$, that is $(D_0.g\mid_{\mathcal U_i})$ followed by $mp_i$ equals the inclusion followed by $\varphi_1$ followed by $D.g$. Let $c'$ be a $k$-linear map on $\Gamma$ of the chart $i_0$ of the base-changed cover, with values in $\operatorname{Hom}_k$ of the dual of $V$ into the group of $1$-cochains of the base-changed cover for the unit $\mathcal O$-module presheaf of `pullback.snd`, which is a derivation at the point $e_1$, i.e. $c'(ab)=\mathrm{ev}(a)c'(b)+\mathrm{ev}(b)c'(a)$ for the evaluation $\mathrm{ev}$ determined by $e_1$. Assume that for each pair $s$ there is $c_s:\Gamma(\text{chart }i_0)\to\operatorname{Hom}_k(V^\ast,k\otimes_B\Gamma(D_0.A,\mathcal U_s))$ which is a system of tangent coordinates, in the sense of `IsTangentCoordsOfPairAt` for the ideal $I$, the module $V$ and $\iota$, for the pair of morphisms $\operatorname{Spec}\Gamma(D_0.A,\mathcal U_s)\to D.A$ given by $mp_{s_0}$ and by $\tau_s$ followed by $mp_{s_1}$, relative to `pullback.snd`, the base change of $D_0.L$ to $k$, the map $j_\kappa$ followed by $D.g$, and the chart $i_0$ — so there are a map $w_0$ from the spectrum of the thickening $(k\otimes_B\Gamma(D_0.A,\mathcal U_s))\otimes_k(k\oplus V)$ over the tangent base, making $w_0$ followed by $j_\kappa$ and $D.g$ a tangent vector of the pair in the sense of `IsTangentOfPair`, and a factorisation $w_1$ through the chart $i_0$ of the translate of $w_0$ by the group law, with $c_s$ the tangent-coordinate function of the ring homomorphism induced by $w_1$ — and assume $\sigma_s\circ c_s$ is the component of $c'$ at $s$. Then $\varphi_1$ extends to $D$, i.e. there is $\varphi:D.A\to D.A$ with $\varphi$ followed by $D.f$ equal to $D.f$ and $\varphi_1$ followed by $D.g$ equal to $D.g$ followed by $\varphi$, if and only if for every section $a$ of the chart $i_0$ on the special fibre and every $\xi\in V^\ast$ the $1$-cochain $c'(a)(\xi)$ lies in the image of the degree-$0$ Čech differential `d` of the unit $\mathcal O$-module presheaf of `pullback.snd` for the base-changed cover.
--
--   This is the Čech-cohomological criterion for extending an endomorphism across a small extension of artinian local base rings, for a deformation obtained from a given one by regluing its charts along automorphisms of the overlaps: the extension exists exactly when the twisted $1$-cochain recording the discrepancy of an arbitrary system of chart-wise lifts is a coboundary. It is used by [`GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare), which restates the coboundary condition as the vanishing of an explicit alternating sum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_forall_mem_range_d_of_isRegluingBy_of_twisted_local_lifts_bare.lean

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
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_forall_mem_range_d_of_isRegluingBy_of_twisted_local_lifts_bare
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

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpf : ∀ i, mp i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)
    (c' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ mp (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ mp (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c'.1 a ξ s) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    (∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ φ₁ ≫ D.g = D.g ≫ φ) ↔
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        c'.1 a ξ ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0) := by sorry
