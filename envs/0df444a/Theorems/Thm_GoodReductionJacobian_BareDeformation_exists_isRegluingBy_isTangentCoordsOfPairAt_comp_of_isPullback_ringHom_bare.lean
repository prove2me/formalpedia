-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/857ed79b-248f-58d5-841a-43113f646ed2
-- title:
--   Tangent class of a base-changed reglued bare deformation
-- statement:
--   The setting is a small extension of Artinian local rings together with a bare deformation of an abelian scheme and an endomorphism of the base.
--
--   *The small extension.* $B$ is a commutative local Artinian ring whose residue field $\kappa = \mathrm{ResidueField}\,B$ is algebraically closed, and $B_1$ is a commutative $B$-algebra such that $\mathrm{algebraMap}\,B\,B_1$ is surjective (`hπ`), its kernel $J$ is a nilpotent ideal (`hker`), $J \cdot \mathfrak m_B = \bot$ (`hsmall`), and $J \le \mathfrak m_B$ (`hI`).
--
--   *The module $V$ and the identification of $J$.* $V$ is a $\kappa$-vector space, finite over $\kappa$, carrying also a $B$-module structure compatible with the $\kappa$-structure through the scalar tower, and a right $\kappa$-action agreeing with the left one. A $B$-linear map $\iota : V \to B$ is given which is injective (`hι`) and whose range is exactly $J$, viewed as a $B$-submodule (`hιI`).
--
--   *The object being deformed.* $f_1 : A_1 \to \operatorname{Spec} B_1$ carries a relative group law $L_1$ which is commutative (`hc₁`), and `h₁` asserts the bundle of abelian-scheme properties for $f_1$: smoothness, properness, connectedness of all fibres, and the existence of a relative group law.
--
--   *The reference deformation and its charts.* $D_0$ is a bare deformation of $(f_1, L_1)$ to $B$: a scheme $D_0.A$ with a structure morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$, the abelian-scheme property bundle over $B$, and a morphism $D_0.g : A_1 \to D_0.A$ making $A_1$ the base change of $D_0.A$ along $B \to B_1$ and compatible with the two group laws; $D_0.f$ is separated. $\mathcal U$ is an ordered affine cover of $D_0.A$ (a finite linearly ordered index set, affine opens $\mathcal U.U\,i$ with supremum $\top$), $i_0$ is an index, and $e_0 : \operatorname{Spec} B \to \mathcal U.U\,i_0$ is a section which, followed by the open inclusion, is the unit section of $D_0.L$ (`he₀`); similarly $e_1 : \operatorname{Spec}\kappa \to (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U\,i_0$ followed by the inclusion is the unit section of the base-changed group law on $X_\kappa = \mathrm{pullback}\,D_0.f\,(\operatorname{Spec}\kappa \to \operatorname{Spec} B)$ (`he₁`).
--
--   *Comparison of overlap rings.* For every $s \in \mathcal U.\mathrm{Idx}\,1$, that is every strictly increasing pair of indices, $\sigma_s$ is a ring isomorphism from $\kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$ onto $\Gamma(X_\kappa, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).\mathrm{inter}\,s)$, where $\mathcal U.\mathrm{inter}\,s$ is the intersection of the two charts indexed by $s$. The hypotheses `hσ₁` and `hσ₂` fix $\sigma_s$ on the two factors: on $1 \otimes x$ it is the pullback of $x$ along $\mathrm{pullback.fst}$ followed by the restriction to the base-changed intersection, and on $a \otimes 1$ it is the image of $a$ under the $\kappa$-algebra structure map of the overlap ring of $X_\kappa$.
--
--   *The tangent class $c$.* With respect to the $\kappa$-algebra structure of $\Gamma(X_\kappa, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U\,i_0)$ coming from the structure morphism $\mathrm{pullback.snd}$, $c$ is an element of $\mathrm{Algebra.PointDerivations}$ at the evaluation homomorphism determined by $e_1$: a $\kappa$-linear map on that ring, with values in $\kappa$-linear maps from the dual $V^\vee = \mathrm{Module.Dual}\,\kappa\,V$ to the group of $1$-cochains of the unit $\mathcal O$-module presheaf of $\mathrm{pullback.snd}$ on the base-changed cover, satisfying the Leibniz rule $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b) \cdot D(a)$. The hypothesis `hc` requires that for all sections $a$ and all $\xi \in V^\vee$ the cochain $c\,a\,\xi$ lies in the kernel of the Čech differential in degree $1$, i.e. is a cocycle.
--
--   *The endomorphism of the base and its lift.* $\varphi : B \to B$ is a ring homomorphism with $(\mathrm{algebraMap}\,B\,B_1)\circ\varphi = \mathrm{algebraMap}\,B\,B_1$ (`hφ`), and $\varphi_V : V \to V$ is $\kappa$-linear with $\iota(\varphi_V v) = \varphi(\iota v)$ for all $v$ (`hφV`). A morphism $k_0 : D_0.A \to D_0.A$ is given which exhibits $D_0.A$ as the base change of itself along $\operatorname{Spec}\varphi$ (`hk₀`: the square formed by $k_0$, $D_0.f$, $D_0.f$ and $\operatorname{Spec}\varphi$ is a pullback), which satisfies $D_0.g$ followed by $k_0$ equals $D_0.g$ (`hk₀g`), preserves every chart, $k_0^{-1}(\mathcal U.U\,a) = \mathcal U.U\,a$ (`hk₀U`), and induces the identity on the special fibre in the sense that $\mathrm{pullback.fst}$ followed by $k_0$ equals $\mathrm{pullback.fst}$ (`hk₀κ`).
--
--   *The reglued deformation and its tangent coordinates.* $\tau$ assigns to each $s \in \mathcal U.\mathrm{Idx}\,1$ an automorphism of the scheme $\mathcal U.\mathrm{inter}\,s$, and $D$ is a bare deformation of $(f_1, L_1)$ to $B$ with `hD` : $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau\ D$, that is: each $\tau_s$ is a morphism over $\operatorname{Spec} B$ and fixes the restriction of $D_0.g$ to the intersection, and there are open immersions of the charts $\mathcal U.U\,i$ into $D.A$, over $D_0.f$, jointly surjective on points, compatible with $D_0.g$, and agreeing on each overlap after insertion of $\tau_s$. The hypothesis `hτ` states that for every $s$ there exists a function $cs$ on $\Gamma(X_\kappa, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U\,i_0)$ with values in $\kappa$-linear maps $V^\vee \to \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$ such that $cs$ is the system of tangent coordinates, in the sense of [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) for the ideal $J$, the module $V$ and $\iota$, of the pair consisting of the canonical map $\operatorname{Spec}\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s) \to D_0.A$ and its twist by $\tau_s$ (namely the inverse of the affine isomorphism followed by $\tau_s$ and the open inclusion), taken at the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U\,i_0$ of the special fibre with its structure morphism $\mathrm{pullback.snd}$, base-changed group law and projection $\mathrm{pullback.fst}$; and moreover $\sigma_s(cs\,a\,\xi) = (c\,a\,\xi)(s)$ for all sections $a$ and all $\xi \in V^\vee$.
--
--   *The base change of $D$.* Finally $D_\varphi$ is a bare deformation of $(f_1, L_1)$ to $B$ together with $h : D_\varphi.A \to D.A$ making the square of $h$, $D_\varphi.f$, $D.f$ and $\operatorname{Spec}\varphi$ a pullback (`hh`), and with $D_\varphi.g$ followed by $h$ equal to $D.g$ (`hhg`).
--
--   *Conclusion.* There exists a family $\tau'$ of automorphisms of the schemes $\mathcal U.\mathrm{inter}\,s$, $s \in \mathcal U.\mathrm{Idx}\,1$, such that:
--
--   (i) $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau'\ D_\varphi$, i.e. $D_\varphi$ is obtained from $D_0$ by regluing the charts of $\mathcal U$ along $\tau'$ in the sense recalled above; and
--
--   (ii) for every $s \in \mathcal U.\mathrm{Idx}\,1$ there exists a function $cs$ on $\Gamma(X_\kappa, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U\,i_0)$ with values in $\kappa$-linear maps $V^\vee \to \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$ such that $cs$ is the system of tangent coordinates, for $J$, $V$, $\iota$, of the pair consisting of the canonical map $\operatorname{Spec}\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s) \to D_0.A$ and the map obtained from the inverse of the affine isomorphism followed by $\tau'_s$ and the open inclusion, taken at the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U\,i_0$ of the special fibre with $\mathrm{pullback.snd}$, the base-changed group law and $\mathrm{pullback.fst}$, and such that
--   $$\sigma_s\bigl(cs\,a\,\xi\bigr) = \bigl(c\,a\,(\xi \circ \varphi_V)\bigr)(s)$$
--   for every section $a$ of the unit chart of the special fibre and every $\xi \in V^\vee$.
--
--   Thus the tangent class of the base-changed deformation $D_\varphi$ is obtained from that of $D$ by precomposing the dual variable with $\varphi_V$.
--
--   This is the functoriality of the tangent (Kodaira–Spencer) class of a bare deformation under an endomorphism $\varphi$ of the small extension $B \to B_1$ inducing $\varphi_V$ on the kernel: base change along $\varphi$ replaces the class $c$ by $c(\,\cdot\,,\ \xi \circ \varphi_V)$. Specialised to $B = \kappa[\varepsilon]$, $B_1 = \kappa$ and $\varphi : \varepsilon \mapsto \lambda\varepsilon$, it supplies the $\kappa$-linearity of the tangent space of the deformation functor, and it is used in the study of deformations of fake elliptic curves in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare
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

    (φ : B →+* B) (hφ : (algebraMap B B₁).comp φ = algebraMap B B₁)
    (φV : V →ₗ[(ResidueField B)] V) (hφV : ∀ v : V, ι (φV v) = φ (ι v))
    (k₀ : D₀.A ⟶ D₀.A) (hk₀ : CategoryTheory.IsPullback k₀ D₀.f D₀.f (Spec.map (CommRingCat.ofHom φ)))
    (hk₀g : D₀.g ≫ k₀ = D₀.g)
    (hk₀U : ∀ a : 𝒰.ι, k₀ ⁻¹ᵁ 𝒰.U a = 𝒰.U a)
    (hk₀κ : pullback.fst D₀.f (specMap B (ResidueField B)) ≫ k₀ = pullback.fst D₀.f (specMap B (ResidueField B)))

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
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

    (Dφ : BareDeformation f₁ L₁ B) (h : Dφ.A ⟶ D.A)
    (hh : CategoryTheory.IsPullback h Dφ.f D.f (Spec.map (CommRingCat.ofHom φ))) (hhg : Dφ.g ≫ h = D.g) :
    ∃ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      D₀.IsRegluingBy 𝒰 τ' Dφ ∧
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ' s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a (ξ ∘ₗ φV) s := by sorry
