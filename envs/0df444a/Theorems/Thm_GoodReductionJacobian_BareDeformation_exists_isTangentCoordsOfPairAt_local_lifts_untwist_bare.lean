-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b0104260-b395-53c5-97fb-8e3d2093fe6f
-- title:
--   Untwisting the twisted lift coordinates on a smaller affine open
-- statement:
--   Throughout, $\kappa$ denotes the residue field `ResidueField B`, $X_\kappa$ the pullback of `D₀.f` along `specMap B (ResidueField B)` (the fibre of `D₀.A` over the closed point), and $\mathcal U_\kappa$ the base change `𝒰.baseChange D₀.f (ResidueField B)` of the cover `𝒰`; for a simplex $s$ of `𝒰`, `𝒰.inter s` is the intersection $\bigcap_j U_{s(j)}$ of the members of `𝒰` indexed by $s$.
--
--   *Ring-theoretic data.* $B$ is a local Artinian ring with algebraically closed residue field, $B_1$ is a $B$-algebra such that `algebraMap B B₁` is surjective (`hπ`), its kernel $I$ is nilpotent (`hker`), satisfies $I\cdot\mathfrak m_B=0$ (`hsmall`) and $I\subseteq\mathfrak m_B$ (`hI`). Further, $V$ is a finite-dimensional $\kappa$-vector space carrying in addition a $B$-module structure compatible with the $\kappa$-structure and an opposite $\kappa$-action agreeing with the given one, and $\iota:V\to B$ is an injective $B$-linear map (`hι`) whose range, viewed as a $B$-submodule, is exactly $I$ (`hιI`).
--
--   *The abelian scheme over $B_1$ and its bare deformations.* $f_1:A_1\to\operatorname{Spec}B_1$ carries a relative group law $L_1$ which is commutative (`hc₁`) and satisfies the bundle of properties `AbelianSchemePropertyBundle B₁ f₁` (smooth, proper, connected fibres, and a relative group law exists) (`h₁`). $D_0$ and $D$ are two elements of `BareDeformation f₁ L₁ B`: each consists of a scheme over $\operatorname{Spec}B$ with a commutative relative group law satisfying the same bundle of properties, together with a morphism from $A_1$ exhibiting $A_1$ as the pullback along $\operatorname{Spec}B_1\to\operatorname{Spec}B$ and compatible with the two group laws. The structure morphism `D₀.f` is separated.
--
--   *Cover and unit charts.* `𝒰` is an ordered affine cover of `D₀.A` (a finite linearly ordered index set, affine opens whose supremum is $\top$), $i_0$ one of its indices, and $e_0:\operatorname{Spec}B\to U_{i_0}$ a section whose composite with the inclusion is the unit section of `D₀.L` (`he₀`); likewise $e_1:\operatorname{Spec}\kappa\to (\mathcal U_\kappa)_{i_0}$ has composite with the inclusion the unit section of the base-changed group law `RelativeGroupLaw.baseChange` of `D₀.L` (`he₁`). The open $(\mathcal U_\kappa)_{i_0}$ is affine (`hU`).
--
--   *Pinned comparison isomorphisms.* For every $1$-simplex $s$ of `𝒰`, $\sigma_s$ is a ring isomorphism $\kappa\otimes_B\Gamma(D_0.A,\mathcal U_s)\cong\Gamma(X_\kappa,(\mathcal U_\kappa)_s)$, normalised by `hσ₁` (on $1\otimes x$ it is the restriction along $(\mathcal U_\kappa)_s\le$ the preimage of $\mathcal U_s$ of the map induced by `pullback.fst`) and `hσ₂` (on $a\otimes 1$ it is the structure map of $\kappa$).
--
--   *The regluing class.* $c$ is a point derivation of $\Gamma(X_\kappa,(\mathcal U_\kappa)_{i_0})$ over $\kappa$ at the $\kappa$-point determined by $e_1$, with values in $\operatorname{Hom}_\kappa(V^{*},C^1)$, where $C^1$ denotes the $\kappa$-module of Čech $1$-cochains `(OModulePresheaf.unit (pullback.snd …)).cochain (𝒰.baseChange …) 1`, i.e. families of sections of the structure sheaf of $X_\kappa$ over the pairwise overlaps of $\mathcal U_\kappa$; `hc` requires every value $c(a)(\xi)$ to be a cocycle, that is, to lie in the kernel of the Čech differential `d … 1`.
--
--   *Transition isomorphisms and the regluing of $D$.* For each $1$-simplex $s$, $\tau_s$ is a self-isomorphism of the scheme $\mathcal U_s$, compatible with the structure morphism to $\operatorname{Spec}B$ (`hτB`) and with the restriction of `D₀.g` (`hτg`). The deformation $D$ is presented by charts: morphisms $\iota_i:U_i\to D.A$ which are open immersions (`hιopen`), lie over $\operatorname{Spec}B$ (`hιf`), are jointly surjective on points (`hιsurj`), are compatible with `D₀.g` and `D.g` (`hιg`), and glue on overlaps through the $\tau_s$ (`hιglue`). The hypothesis `hτ` states that for every $1$-simplex $s$ there are chart coordinates $c_s$ on $\Gamma(X_\kappa,(\mathcal U_\kappa)_{i_0})$ with values in $\operatorname{Hom}_\kappa(V^{*},\kappa\otimes_B\Gamma(D_0.A,\mathcal U_s))$ such that `IsTangentCoordsOfPairAt I V ι Γ(D₀.A, 𝒰.inter s)` holds for the pair consisting of the canonical map `fromSpec` of the affine open $\mathcal U_s$ and of `isoSpec.inv` followed by $\tau_s$ followed by the inclusion, taken relative to `pullback.snd`, the base-changed group law, the map `pullback.fst` and the open $(\mathcal U_\kappa)_{i_0}$, and such that $\sigma_s(c_s(a)(\xi))$ is the $s$-component of $c(a)(\xi)$. Here `IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c` asserts the existence of a point $w_0$ of the ambient scheme with values in the thickening $(\kappa\otimes_{B}C)\otimes_\kappa(\kappa\oplus V)$ lying over the base, and of a lift $w_1$ into $Ue$ of the group-law translate of $w_0$ to the unit, such that the pair $(u,v)$ is an `IsTangentOfPair` for $I,V,\iota,C$ along $w_0$ followed by $ak$ (both maps factor through the spectrum of the pair ring by a Schlessinger map), and such that $c$ is the `tangentCoords` function attached to the chart ring homomorphism of $w_1$.
--
--   *Tangent presentation.* $W$ is a $\kappa$-vector space, $\tau_W$ an injective map (`hWinj`) from $W$ to the morphisms $\operatorname{Spec}\kappa[\varepsilon]\to X_\kappa$ over `tangentBase`, whose image consists precisely of the tangent vectors of the base-changed group law (`hWrange`), which is additive for that group law (`hWadd`) and turns scalar multiplication into precomposition with `tangentScale` (`hWsmul`). $\Phi$ is a family, natural in the $\kappa$-module $M$ (`hΦnat`), of $\kappa$-linear isomorphisms from the $M$-valued point derivations of $\Gamma(X_\kappa,(\mathcal U_\kappa)_{i_0})$ at the unit onto $W\otimes_\kappa M$, pinned geometrically by `hΦpin`: for a $\kappa$-valued point derivation $\delta$ and a ring homomorphism $\chi$ into the dual numbers whose first component is the evaluation at the unit and whose second component is $\delta$, the tangent vector attached to $\Phi(\kappa)(\delta)$ under the right unitor equals $\operatorname{Spec}\chi$ followed by `hU.fromSpec`.
--
--   *Endomorphism data.* $\varphi_1$ is an endomorphism of $A_1$ over $\operatorname{Spec}B_1$ (`hφ₁`); $j_\kappa:X_\kappa\to A_1$ satisfies $j_\kappa$ followed by `D₀.g` $=$ `pullback.fst` (`hjκ`); $\psi$ is an endomorphism of $X_\kappa$ over $\operatorname{Spec}\kappa$ (`hψ`) compatible with $j_\kappa$ and $\varphi_1$ (`hψ₁`) and a homomorphism for the base-changed group law in the sense of `pushPt` (`hψhom`); $\theta_\psi:W\to W$ is $\kappa$-linear with $\tau_W(\theta_\psi w)=$ `pushPt ψ hψ` $(\tau_W w)$ (`hθψ`).
--
--   *Local lifts and their cochains.* The morphisms $m_i:U_i\to D_0.A$ lie over $\operatorname{Spec}B$ (`hmf`) and lift $\varphi_1$ on the fibre over $B_1$ (`hmμ`); $c_0$ is a point derivation with values in $\operatorname{Hom}_\kappa(V^{*},C^1)$ whose $s$-components are, through $\sigma_s$, the coordinates of the pair $(m_{s(0)},m_{s(1)})$ restricted to $\mathcal U_s$ in the sense of `IsTangentCoordsOfPairAt` relative to `pullback.fst` (`hc₀`), and all of whose values are Čech cocycles (`hc₀Z`). Similarly $m'_i:U_i\to D.A$ lie over $\operatorname{Spec}B$ (`hmpf`) and lift $\varphi_1$ (`hmpμ`), and $c'$ is a point derivation with values in $\operatorname{Hom}_\kappa(V^{*},C^1)$ whose $s$-components are, through $\sigma_s$, the coordinates of the $\tau$-twisted pair $(m'_{s(0)},\ \tau_s$ followed by $m'_{s(1)})$ on $\mathcal U_s$, taken relative to `pullback.snd`, the base-changed group law, the map $j_\kappa$ followed by `D.g`, and the open $(\mathcal U_\kappa)_{i_0}$ (`hc'`).
--
--   *The local datum.* Finally $t$ is a $1$-simplex of `𝒰`, $W_{\mathrm o}$ an affine open of `D₀.A` (`hWo`) contained in $\mathcal U_t$ (`hWt`), and $c'_t$ a function on $\Gamma(X_\kappa,(\mathcal U_\kappa)_{i_0})$ with values in $\operatorname{Hom}_\kappa(V^{*},\kappa\otimes_B\Gamma(D_0.A,\mathcal U_t))$ which (`hcs'`) is a system of tangent coordinates in the above sense for the twisted pair consisting of `isoSpec.inv` followed by the inclusion $\mathcal U_t\le U_{t(0)}$ and $m'_{t(0)}$, and of `isoSpec.inv` followed by $\tau_t$, the inclusion $\mathcal U_t\le U_{t(1)}$ and $m'_{t(1)}$, relative to `pullback.snd`, the base-changed group law, $j_\kappa$ followed by `D.g`, and $(\mathcal U_\kappa)_{i_0}$.
--
--   *Conclusion.* There exist functions $y$ on $\Gamma(X_\kappa,(\mathcal U_\kappa)_{i_0})$ with values in $\operatorname{Hom}_\kappa(V^{*},\kappa\otimes_B\Gamma(D_0.A,W_{\mathrm o}))$ and $x^\theta$ on the same ring with values in $\operatorname{Hom}_\kappa(V^{*},\kappa\otimes_B\Gamma(D_0.A,\mathcal U_t))$ such that the following three statements hold.
--
--   First, `IsTangentCoordsOfPairAt I V ι Γ(D₀.A, Wo)` holds, with coordinates $y$, for the *untwisted* pair consisting of `hWo.isoSpec.inv` followed by the inclusion $W_{\mathrm o}\le U_{t(0)}$ and $m'_{t(0)}$, and of `hWo.isoSpec.inv` followed by the inclusion $W_{\mathrm o}\le U_{t(1)}$ and $m'_{t(1)}$, taken relative to `pullback.snd`, the base-changed group law, $j_\kappa$ followed by `D.g`, and the open $(\mathcal U_\kappa)_{i_0}$.
--
--   Secondly, for all $a\in\Gamma(X_\kappa,(\mathcal U_\kappa)_{i_0})$ and all $\xi\in V^{*}$,
--   $$\sigma_t\bigl(x^\theta(a)(\xi)\bigr)=\Bigl(\Phi(M)^{-1}\bigl((\theta_\psi\otimes\mathrm{id}_{M})\,\Phi(M)(c)\bigr)\Bigr)(a)(\xi)_t,$$
--   where $M=\operatorname{Hom}_\kappa(V^{*},C^1)$ and the subscript $t$ denotes the component of the $1$-cochain at the simplex $t$; that is, $x^\theta$ is pinned to the $t$-component of the image of the regluing class $c$ under $\theta_\psi$.
--
--   Thirdly, for every $a\in\Gamma(X_\kappa,(\mathcal U_\kappa)_{i_0})$, writing $r$ for the restriction $\kappa\otimes_B\Gamma(D_0.A,\mathcal U_t)\to\kappa\otimes_B\Gamma(D_0.A,W_{\mathrm o})$ obtained by tensoring the identity of $\kappa$ with `restrictAlgHom D₀.f hWt`,
--   $$r\circ c'_t(a)=y(a)+r\circ x^\theta(a).$$
--
--   This is the untwisting step in the comparison of the obstruction cocycles attached to two bare deformations of an abelian scheme along a small extension of local Artinian rings: restricted to an affine open inside an overlap chart, the tangent coordinates of the $\tau$-twisted pair of lifts of the endomorphism $\varphi_1$ to $D$ split as the coordinates of the untwisted pair plus the $\theta_\psi$-transform of the regluing class $c$. It is used in the two statements computing the Čech differential of the obstruction cocycle of a factoring system of local lifts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
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
    (D : BareDeformation f₁ L₁ B)

    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A) (hιopen : ∀ i, IsOpenImmersion (ιD i))
    (hιf : ∀ i, ιD i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hιsurj : ∀ x : D.A, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιD i).base y = x)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)
    (hιglue : ∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιD (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιD (s.1 1))
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
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = (c₀ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) a ξ s)
    (hc₀Z : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀.1 a ξ) = 0)

    (θψ : W →ₗ[(ResidueField B)] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

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
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c'.1 a ξ s)

    (t : 𝒰.Idx 1) (Wo : D₀.A.Opens) (hWo : IsAffineOpen Wo) (hWt : Wo ≤ 𝒰.inter t)
    (cs' : letI := algebraOfHom D₀.f (𝒰.inter t)
      Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))))
    (hcs' : letI := algebraOfHom D₀.f (𝒰.inter t)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 0) ≫ mp (t.1 0))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv ≫ (τ t).hom ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs') :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    letI := algebraOfHom D₀.f (𝒰.inter t)
    letI := algebraOfHom D₀.f Wo
    ∃ (y : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, Wo))))
      (xθ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t)))),
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, Wo)
        (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 0)) ≫ mp (t.1 0))
        (hWo.isoSpec.inv ≫ D₀.A.homOfLE (hWt.trans (𝒰.inter_le t 1)) ≫ mp (t.1 1))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) y ∧
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ t (xθ a ξ) = (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c)))).1 a ξ t) ∧
      ∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)),
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hWt)).toLinearMap ∘ₗ cs' a =
          y a + (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f hWt)).toLinearMap ∘ₗ xθ a := by sorry
