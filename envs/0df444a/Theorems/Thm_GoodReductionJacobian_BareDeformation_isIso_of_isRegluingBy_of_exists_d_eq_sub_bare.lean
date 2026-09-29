-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_isIso_of_isRegluingBy_of_exists_d_eq_sub_bare
-- name    : GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_exists_d_eq_sub_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c706f9bc-84b4-58b5-9975-8a112203e1be
-- title:
--   Regluings with cohomologous tangent cocycles give isomorphic deformations
-- statement:
--   Throughout, $k$ denotes the residue field `ResidueField B`.
--
--   **Rings.** $B$ is an Artinian local ring with algebraically closed residue field and $B_1$ is a $B$-algebra. The hypotheses on the structure map are: `hπ`, the algebra map $B \to B_1$ is surjective; `hker`, its kernel $I := \ker(B \to B_1)$ is nilpotent; `hsmall`, $I \cdot \mathfrak m_B = 0$; and `hI`, $I \subseteq \mathfrak m_B$ (so $B \to B_1$ is a small extension).
--
--   **The object over $B_1$.** $f_1 : A_1 \to \operatorname{Spec} B_1$ is a morphism of schemes, $L_1$ a `RelativeGroupLaw` for it (functorial group structure on the sets of sections of $f_1$ over arbitrary $B_1$-schemes, natural in the base), `hc₁` asserts that $L_1$ is commutative, and `h₁` is the bundle `AbelianSchemePropertyBundle B₁ f₁`, i.e. $f_1$ is smooth and proper, all its fibres are connected, and it carries some relative group law.
--
--   **The tangent module.** $V$ is a finite-dimensional $k$-vector space, also a $B$-module compatibly with the tower $B \to k$, with the matching right/central scalar structures; $\iota : V \to B$ is an injective $B$-linear map (`hι`) whose range is exactly $I$, viewed as a $B$-submodule (`hιI`). Thus $V \cong I$ as a $B$-module.
--
--   **The reference deformation and its cover.** $D_0$ is a `BareDeformation f₁ L₁ B`: a scheme $D_0.A$ with a morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$, the abelian-scheme property bundle for $D_0.f$, and a morphism $g : A_1 \to D_0.A$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the two group laws. It is assumed that $D_0.f$ is separated. Further, $\mathcal U$ is an `OrderedAffineCover` of $D_0.A$ (a finite linearly ordered family of affine opens covering $D_0.A$), $i_0$ an index of $\mathcal U$, and $e_0 : \operatorname{Spec} B \to U_{i_0}$ a morphism whose composite with the open immersion $U_{i_0} \hookrightarrow D_0.A$ is the unit section of $D_0.L$ (`he₀`). For $s$ ranging over $\mathcal U.\mathrm{Idx}\,1$, the strictly increasing pairs of indices, $\mathcal U.\mathrm{inter}\,s$ denotes the corresponding pairwise intersection.
--
--   **The special fibre.** Write $A_k$ for the pullback of $D_0.f$ along $\operatorname{Spec} k \to \operatorname{Spec} B$ and $\mathcal U_k := \mathcal U.\mathrm{baseChange}$ for the cover of $A_k$ obtained by pulling back the opens of $\mathcal U$ along the first projection. Then $e_1 : \operatorname{Spec} k \to (\mathcal U_k).U\,i_0$ is a morphism whose composite with the inclusion is the unit section of the base-changed group law `RelativeGroupLaw.baseChange` of $D_0.L$ (`he₁`). The family $\sigma$ gives, for each $s$, a ring isomorphism $k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(A_k, (\mathcal U_k).\mathrm{inter}\,s)$; the hypotheses `hσ₁` and `hσ₂` pin it down as the canonical base-change comparison, namely $\sigma_s(1 \otimes x)$ is the restriction to $(\mathcal U_k).\mathrm{inter}\,s$ of the pullback of $x$ along the first projection, and $\sigma_s(a \otimes 1)$ is the image of $a \in k$ under the structure map of the second projection.
--
--   **The two cocycles.** Let $C^i$ denote the $i$-cochains `(OModulePresheaf.unit (pullback.snd …)).cochain` of the cover $\mathcal U_k$ with values in the structure-sheaf presheaf, with differentials $d^i$. The data $c$ and $c'$ are each an element of $\mathrm{PointDerivations}_k$ of the ring $\Gamma(A_k, (\mathcal U_k).U\,i_0)$ at the evaluation homomorphism determined by $e_1$, with values in the $k$-module $\operatorname{Hom}_k(V^{*}, C^{1})$; that is, each is a $k$-linear map $D$ from $\Gamma(A_k, (\mathcal U_k).U\,i_0)$ to $\operatorname{Hom}_k(V^{*}, C^{1})$ satisfying the Leibniz rule $D(ab) = \mathrm{ev}(a)\,D(b) + \mathrm{ev}(b)\,D(a)$ at that point. The hypotheses `hc` and `hc'` state that for every section $a$ and every $\xi \in V^{*} = \operatorname{Hom}_k(V,k)$ the $1$-cochains $c(a)(\xi)$ and $c'(a)(\xi)$ lie in $\ker d^1$, i.e. are Čech $1$-cocycles.
--
--   **The two regluings.** $\tau$ and $\tau'$ assign to each $s$ a self-isomorphism of the scheme $\mathcal U.\mathrm{inter}\,s$, and $D$, $D'$ are bare deformations of $f_1, L_1$ over $B$ with `hD`: $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau\ D$ and `hD'`: $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau'\ D'$. Unfolded, $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau\ D$ says: each $\tau_s$ is a morphism over $\operatorname{Spec} B$ and fixes the restriction of $D_0.g$ to $\mathcal U.\mathrm{inter}\,s$; and there is a family of morphisms $U_i \to D.A$, each an open immersion, each compatible with the structure maps to $\operatorname{Spec} B$ and with $D_0.g$, jointly surjective on points, and such that on each overlap the two charts agree after insertion of $\tau_s$.
--
--   **Matching of $\tau, \tau'$ with $c, c'$.** The hypothesis `hτ` states that for each $s$ there is a function $c_s$ from $\Gamma(A_k, (\mathcal U_k).U\,i_0)$ to $\operatorname{Hom}_k(V^{*}, k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ such that, first, `IsTangentCoordsOfPairAt` holds for the ideal $I$, the module $V$, the map $\iota$, the ring $C = \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, the pair of morphisms given by `fromSpec` of the affine open $\mathcal U.\mathrm{inter}\,s$ and by $\mathrm{isoSpec}^{-1}$ followed by $\tau_s$ followed by the open immersion, the second projection of the base change as structure map of $A_k$, the base-changed group law, the first projection, the open $(\mathcal U_k).U\,i_0$, and the coordinates $c_s$ — i.e. there are a morphism $w_0$ from the spectrum of the thickening $(k \otimes_B C) \otimes_k (k \oplus V)$ to $A_k$ over the base, and a morphism $w_1$ into $(\mathcal U_k).U\,i_0$, such that $w_0$ followed by the first projection is a tangent vector of the given pair in the sense of `IsTangentOfPair` for $I, V, \iota, C$, such that $w_1$ followed by the inclusion is the group-law translate of $w_0$ to the unit section, and such that $c_s$ is the coordinate function `tangentCoords` of the chart ring homomorphism attached to $w_1$; and, second, $\sigma_s(c_s(a)(\xi)) = c(a)(\xi)_s$ for all $a$ and all $\xi \in V^{*}$. The hypothesis `hτ'` is the same statement with $\tau'$ in place of $\tau$ and $c'$ in place of $c$.
--
--   **Coboundary hypothesis.** `hcob`: for every section $a$ of $\Gamma(A_k, (\mathcal U_k).U\,i_0)$ and every $\xi \in V^{*}$ there is a $0$-cochain $b \in C^{0}$ with $d^0 b = c(a)(\xi) - c'(a)(\xi)$.
--
--   **Conclusion.** $D.\mathrm{IsIso}\ D'$: there exists an isomorphism of schemes $e : D.A \cong D'.A$ such that $e$ followed by $D'.f$ equals $D.f$, and $D.g$ followed by $e$ equals $D'.g$.
--
--   This is the comparison step in the Čech-theoretic description of bare deformations of an abelian scheme over a small extension of Artinian local rings: two regluings of the same reference deformation $D_0$ along overlap automorphisms whose tangent coordinate cocycles differ by a coboundary define isomorphic deformations. It is obtained from the chart-level criterion [`GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_forall_comp_hom_eq`](thm.html#GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_forall_comp_hom_eq) together with [`GoodReductionJacobian.BareDeformation.exists_chartIso_comp_eq_of_isRegluingBy_of_exists_d_eq_sub`](thm.html#GoodReductionJacobian.BareDeformation.exists_chartIso_comp_eq_of_isRegluingBy_of_exists_d_eq_sub), and it is used in the Čerednik–Drinfeld part of the development, in the analysis of dual-number deformations of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_isIso_of_isRegluingBy_of_exists_d_eq_sub_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_exists_d_eq_sub_bare
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
    (hcob : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 0,
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0 b =
          (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
          - (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ) :
    D.IsIso D' := by sorry
