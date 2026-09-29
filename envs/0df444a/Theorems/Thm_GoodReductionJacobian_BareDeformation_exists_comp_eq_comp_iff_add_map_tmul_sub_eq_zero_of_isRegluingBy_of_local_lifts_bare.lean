-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b4a8ac0f-fdca-5b80-b7cf-23b6f7c70846
-- title:
--   Lifting an endomorphism to a re-glued deformation: obstruction criterion
-- statement:
--   Setting. Let $B$ be an Artinian local ring with algebraically closed residue field $\kappa =$ `ResidueField B`, and let $B_1$ be a $B$-algebra such that the structure map $B \to B_1$ is surjective (`hπ`), has nilpotent kernel $J :=$ `RingHom.ker (algebraMap B B₁)` (`hker`), and satisfies the smallness condition $J \cdot \mathfrak m_B = 0$ (`hsmall`), together with $J \subseteq \mathfrak m_B$ (`hI`). Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$ that is commutative (`hc₁`) and satisfy `AbelianSchemePropertyBundle B₁ f₁` (`h₁`), i.e. $f_1$ is smooth and proper, all fibres of $f_1$ are connected, and $f_1$ admits a relative group law. Let $V$ be a finite-dimensional $\kappa$-vector space, equipped compatibly with $B$-module and right $\kappa$-module structures, and let $\iota : V \to B$ be an injective $B$-linear map (`hι`) whose range is $J$ viewed as a $B$-submodule (`hιI`).
--
--   Let $D_0$ be a `BareDeformation` of $(f_1, L_1)$ to $B$: a scheme $D_0.A$ with a structure morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$, the abelian-scheme property bundle, and a morphism $D_0.g : A_1 \to D_0.A$ making $A_1$ the base change of $D_0.A$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the group laws on points. The morphism $D_0.f$ is assumed separated. Let $\mathcal U$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered index set $\mathcal U.\iota$, affine opens $\mathcal U.U i$ covering $D_0.A$), with a distinguished index $i_0$ and a section $e_0 : \operatorname{Spec} B \to \mathcal U.U i_0$ whose composite with the inclusion is the unit section of $D_0.L$ (`he₀`). Write $X_\kappa = D_0.A \times_{\operatorname{Spec} B} \operatorname{Spec} \kappa$, with its induced cover $\mathcal U_\kappa = \mathcal U.\mathrm{baseChange}$ (preimages of the $\mathcal U.U i$ under the first projection) and its base-changed group law $L_\kappa =$ `RelativeGroupLaw.baseChange`. Further data: a section $e_1$ of $\mathcal U_\kappa.U i_0$ whose composite with the inclusion is the unit of $L_\kappa$ (`he₁`); ring isomorphisms $\sigma_s : \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\, s) \cong \Gamma(X_\kappa, \mathcal U_\kappa.\mathrm{inter}\, s)$ for each pair index $s \in \mathcal U.\mathrm{Idx}\,1$, normalised by `hσ₁` (on $1 \otimes x$ they agree with restriction of the pullback along the first projection) and `hσ₂` (on $a \otimes 1$ they are the structure map of $\kappa$).
--
--   Tangent cochain data. Let $c$ be a point derivation at $e_1$ of $\Gamma(X_\kappa, \mathcal U_\kappa.U i_0)$ over $\kappa$ — an element of [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9), i.e. a $\kappa$-linear map satisfying the Leibniz rule with respect to evaluation at $e_1$ — with values in $\operatorname{Hom}_\kappa(V^\vee, C^1)$, where $C^1 = (\mathrm{OModulePresheaf.unit}\ \pi_{X_\kappa}).\mathrm{cochain}\ \mathcal U_\kappa\ 1$ is the group of Čech $1$-cochains of the structure presheaf on $\mathcal U_\kappa$; the hypothesis `hc` asserts that all values $c(a)(\xi)$ are Čech cocycles, that is, lie in the kernel of the differential $d^1$.
--
--   Re-gluing. Let $\tau$ assign to each pair index $s$ an automorphism of the scheme $\mathcal U.\mathrm{inter}\,s$, and let $D$ be a second bare deformation with `hD : D₀.IsRegluingBy 𝒰 τ D`: each $\tau_s$ is a morphism over $\operatorname{Spec} B$, commutes with the restriction of $D_0.g$ to $\mathcal U.\mathrm{inter}\,s$, and there are open immersions $\iota_i : \mathcal U.U i \to D.A$ over $\operatorname{Spec} B$ which are jointly surjective, are compatible with $D_0.g$ and $D.g$, and satisfy the $\tau$-twisted gluing relations on overlaps. The hypothesis `hτ` states that $c$ is the system of tangent coordinates of the re-gluing: for each $s$ there are coordinates $c_s$ with values in $\operatorname{Hom}_\kappa(V^\vee, \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ such that `IsTangentCoordsOfPairAt` holds for the pair consisting of the canonical chart map and its $\tau_s$-twist, relative to $J$, $V$, $\iota$, the special fibre $\pi_{X_\kappa}$, $L_\kappa$ and the chart $\mathcal U_\kappa.U i_0$, and such that $\sigma_s(c_s(a)(\xi))$ equals the $s$-component of $c(a)(\xi)$.
--
--   Tangent space and derivation model. The chart $\mathcal U_\kappa.U i_0$ is affine (`hU`). Let $W$ be a $\kappa$-vector space and $\tau_W$ an injective map (`hWinj`) from $W$ to morphisms into $X_\kappa$ over the dual-number base `tangentBase κ (RingHom.id κ)`, whose image consists exactly of the tangent vectors of $L_\kappa$ at the origin (`hWrange`, via `IsTangentVector`), and which is additive for the group law (`hWadd`) and compatible with scaling by `tangentScale` (`hWsmul`). Let $\Phi$ be a family of $\kappa$-linear isomorphisms $\Phi_M : \mathrm{Der}_{e_1}(\Gamma(X_\kappa, \mathcal U_\kappa.U i_0), M) \cong W \otimes_\kappa M$, natural in $M$ (`hΦnat`: $\Phi_{M'}$ applied to the pushforward of a derivation along $g : M \to M'$ equals $\mathrm{id}_W \otimes g$ applied to $\Phi_M$), and pinned on dual-number points (`hΦpin`: for a derivation $\delta$ with values in $\kappa$ and a ring map $\chi$ to $\kappa[\varepsilon]$ whose first component is evaluation at $e_1$ and whose second component is $\delta$, the tangent vector $\tau_W$ of $\Phi_\kappa(\delta)$, transported along the right unitor, is the morphism $\operatorname{Spec}\chi$ followed by `hU.fromSpec`).
--
--   The endomorphism and its local lifts. Let $\varphi_1 : A_1 \to A_1$ be a morphism over $\operatorname{Spec} B_1$ (`hφ₁`); let $j_\kappa : X_\kappa \to A_1$ factor the first projection ($j_\kappa$ followed by $D_0.g$ equals $\mathrm{pr}_1$, `hjκ`); let $\psi : X_\kappa \to X_\kappa$ be a morphism over $\operatorname{Spec}\kappa$ (`hψ`) with $\psi$ followed by $j_\kappa$ equal to $j_\kappa$ followed by $\varphi_1$ (`hψ₁`), and such that $\psi$ is a homomorphism on points: for all test objects, `pushPt ψ hψ` commutes with the multiplication of $L_\kappa$ (`hψhom`). Let $m_i : \mathcal U.U i \to D_0.A$ be morphisms over $\operatorname{Spec} B$ (`hmf`) whose restrictions along $D_0.g$ agree with $\varphi_1$ followed by $D_0.g$ (`hmμ`): these are local lifts of $\varphi_1$ to $D_0$ on the charts of $\mathcal U$. Let $c_0$ be a point derivation at $e_1$ with values in $\operatorname{Hom}_\kappa(V^\vee, C^1)$ whose components are the tangent coordinates of the pairs $(m_{s_0}, m_{s_1})$ on overlaps: `hc₀` asserts, for each pair index $s$, the existence of coordinates $c_s$ with `IsTangentCoordsOfPairAt` for the two chart maps obtained from $m(s_0)$ and $m(s_1)$, matching $c_0$ through $\sigma_s$; and `hc₀Z` asserts that all values $c_0(a)(\xi)$ are annihilated by $d^1$.
--
--   Cohomological data. Let $\theta_\psi : W \to W$ be the $\kappa$-linear map induced by $\psi$ on tangent vectors, characterised by $\tau_W(\theta_\psi w) = \mathrm{pushPt}\ \psi\ (\tau_W w)$ (`hθψ`). Let $H_1$ be a $\kappa$-vector space and $\mathrm{cls}_1$ a surjective $\kappa$-linear map (`hcls₁`) from $\ker d^1$ onto $H_1$ whose kernel is exactly the image of $d^0$ (`hcls₁0`), so that $H_1$ realises the first Čech cohomology of the structure sheaf on $\mathcal U_\kappa$. Let $\rho_\psi : H_1 \to H_1$ be an endomorphism implementing pullback along $\psi$ in the sense of `hρψ`: whenever a refinement $\mathcal V$, index maps $\mathrm{lam}, \mathrm{lam}'$ subordinate to $\psi$ and to the identity respectively, and cocycles $z, z'$ are such that the difference of the pullbacks `unitPullback` of $z$ along $\psi$ and of $z'$ along the identity is a coboundary on $\mathcal V$, then $\rho_\psi(\mathrm{cls}_1 z) = \mathrm{cls}_1 z'$.
--
--   Conclusion. For all point derivations $\hat c, \hat c_0$ at $e_1$ with values in $\operatorname{Hom}_\kappa(V^\vee, \ker d^1)$ such that the underlying cochain of $\hat c_0(a)(\xi)$ is $c_0(a)(\xi)$ for all $a$ and $\xi$, and the underlying cochain of $\hat c(a)(\xi)$ is $c(a)(\xi)$ for all $a$ and $\xi$, the following two assertions are equivalent:
--
--   (i) there exists $\varphi : D.A \to D.A$ with $\varphi$ followed by $D.f$ equal to $D.f$, and $\varphi_1$ followed by $D.g$ equal to $D.g$ followed by $\varphi$;
--
--   (ii) the element
--   $$\Phi\bigl(\mathrm{cls}_1{}_* \hat c_0\bigr) + (\theta_\psi \otimes \mathrm{id})\,\Phi\bigl(\mathrm{cls}_1{}_* \hat c\bigr) - (\mathrm{id}_W \otimes \rho_\psi{}_*)\,\Phi\bigl(\mathrm{cls}_1{}_* \hat c\bigr)$$
--   of $W \otimes_\kappa \operatorname{Hom}_\kappa(V^\vee, H_1)$ vanishes. Here $\mathrm{cls}_1{}_*$ denotes [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) applied to post-composition with $\mathrm{cls}_1$ (that is, `LinearMap.llcomp` with $\mathrm{cls}_1$), $\Phi$ is taken with $M = \operatorname{Hom}_\kappa(V^\vee, H_1)$, and $\rho_\psi{}_*$ is post-composition with $\rho_\psi$ on $\operatorname{Hom}_\kappa(V^\vee, H_1)$.
--
--   This is the Kodaira–Spencer lifting criterion for a morphism, in the case where the same deformation serves as source and target: an endomorphism $\varphi_1$ of the abelian scheme $A_1/B_1$, given with local lifts $m_i$ to the bare deformation $D_0$ over $B$, extends to the deformation $D$ obtained by re-gluing $D_0$ along $\tau$ with tangent class $c$ precisely when the combined obstruction $[c_0] + (\theta_\psi \otimes 1)[c] - (1 \otimes \rho_\psi)[c]$ vanishes in $W \otimes_\kappa \operatorname{Hom}_\kappa(V^\vee, H^1)$. It is used in the construction of lifts of Hecke and Galois endomorphisms to deformations of Jacobians with good reduction, and is cited by the deduction of the corresponding criterion under a global lift and by the existence statement for endomorphism lifts over small extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare
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

    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
    (W : Type) [AddCommGroup W] [Module (ResidueField B) W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))), P ∈ Set.range τW ↔ IsTangentVector (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (ResidueField B) (RingHom.id (ResidueField B)) P)
    (hWadd : ∀ v w : W, τW (v + w) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField B)) (v : W), (τW (a • v)).1 = tangentScale (ResidueField B) a ≫ (τW v).1)

    (Φ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M : Type) [AddCommGroup M] [Module (ResidueField B) M], ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M) ≃ₗ[(ResidueField B)] (W ⊗[(ResidueField B)] M))
    (hΦnat : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M M' : Type) [AddCommGroup M] [Module (ResidueField B) M] [AddCommGroup M'] [Module (ResidueField B) M'] (g : M →ₗ[(ResidueField B)] M') (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (ResidueField B))) (χ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →+* DualNumber (ResidueField B)),
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.fst (χ a) = ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) a) →
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.snd (χ a) = (δ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (ResidueField B)) a) →
        (τW (TensorProduct.rid (ResidueField B) W (Φ (ResidueField B) δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec)

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ : ψ ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)
    (hψhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt ψ hψ ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)
    (c₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c₀.1 a ξ s)
    (hc₀Z : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀.1 a ξ) = 0)

    (θψ : W →ₗ[(ResidueField B)] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (H₁ : Type) [AddCommGroup H₁] [Module (ResidueField B) H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0))
    (ρψ : H₁ →ₗ[(ResidueField B)] H₁)
    (hρψ : ∀ (𝒱 : (pullback D₀.f (specMap B (ResidueField B))).OrderedAffineCover) (lam lam' : 𝒱.ι → (𝒰.baseChange D₀.f (ResidueField B)).ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))),
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam' hl' (0 + 1) z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d 𝒱 0) →
        ρψ (cls₁ z) = cls₁ z') :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)

    ∀ (ĉ ĉ₀ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀.1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c.1 a ξ) →
      ((∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ φ₁ ≫ D.g = D.g ≫ φ) ↔

        (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀)) +
          (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁))
              (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ)) -
            TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) H₁ H₁ ρψ)
              (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ))) = 0) := by sorry
