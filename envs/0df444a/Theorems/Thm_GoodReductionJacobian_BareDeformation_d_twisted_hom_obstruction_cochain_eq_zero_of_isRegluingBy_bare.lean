-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare
-- name    : GoodReductionJacobian.BareDeformation.d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/e2fe9e4c-2af5-5f4b-adc6-7757b0f64da3
-- title:
--   τ-twisted obstruction cochain of local lifts is a cocycle
-- statement:
--   Throughout, write $I := \ker(B \to B_1)$, $k := \mathrm{ResidueField}\,B$, and, for a bare deformation $D_0$, write $X_\kappa := \mathrm{pullback}\ D_0.f\ (\mathrm{specMap}\ B\ k)$ for the base change of $D_0.A$ to $\operatorname{Spec} k$, with its two projections $\mathrm{pullback.fst} : X_\kappa \to D_0.A$ and $\mathrm{pullback.snd} : X_\kappa \to \operatorname{Spec} k$.
--
--   **Base rings.** $B$ is an artinian local ring with algebraically closed residue field, $B_1$ is a commutative $B$-algebra, the structure map $B \to B_1$ is surjective (`hπ`) with nilpotent kernel (`hker`), and $I \cdot \mathfrak{m}_B = 0$ (`hsmall`), together with $I \le \mathfrak{m}_B$ (`hI`).
--
--   **The scheme over $B_1$.** $f_1 : A_1 \to \operatorname{Spec} B_1$ carries a relative group law $L_1$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} B_1$, natural in $T$) which is commutative (`hc₁`), and `h₁ : AbelianSchemePropertyBundle B₁ f₁` records that $f_1$ is smooth and proper, has connected fibres, and admits a relative group law.
--
--   **The tangent module.** $V$ is a finite-dimensional $k$-vector space, with a $B$-module structure compatible with the $k$-structure along $B \to k$ and with the right $k$-action equal to the left one, and $\iota : V \to_{B} B$ is an injective $B$-linear map (`hι`) whose image is exactly $I$, viewed as a $B$-submodule (`hιI`).
--
--   **The deformation $D_0$ and its cover.** $D_0$ is a bare deformation of $(f_1, L_1)$ over $B$: a scheme $D_0.A$ with a structure morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$, the bundle of abelian-scheme properties for $D_0.f$, and a morphism $D_0.g : A_1 \to D_0.A$ making $A_1$ the base change of $D_0.A$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the two group laws on points. The morphism $D_0.f$ is separated. $\mathcal{U}$ is an ordered affine cover of $D_0.A$: a finite linearly ordered index set, affine opens $\mathcal{U}.U\,i$ whose supremum is the whole space; for $i \ge 0$ the $i$-simplices $\mathcal{U}.\mathrm{Idx}\,i$ are the strictly monotone $(i+1)$-tuples $s$ of indices, and $\mathcal{U}.\mathrm{inter}\,s$ is the intersection of the corresponding opens. $i_0$ is an index, and $e_0 : \operatorname{Spec} B \to \mathcal{U}.U\,i_0$ is a morphism which, followed by the open inclusion, is the unit section of $D_0.L$ (`he₀`). Likewise $e_1 : \operatorname{Spec} k \to (\mathcal{U}_\kappa).U\,i_0$, where $\mathcal{U}_\kappa := \mathcal{U}.\mathrm{baseChange}\ D_0.f\ k$ is the cover of $X_\kappa$ obtained by pulling the opens back along $\mathrm{pullback.fst}$, satisfies that $e_1$ followed by the open inclusion is the unit section of the base-changed group law $\mathrm{RelativeGroupLaw.baseChange}$ of $D_0.L$ (`he₁`).
--
--   **Identification of the reductions of the sections over the edges.** For each $1$-simplex $s$, $\sigma\,s$ is a ring isomorphism $k \otimes_B \Gamma(D_0.A, \mathcal{U}.\mathrm{inter}\,s) \cong \Gamma(X_\kappa, \mathcal{U}_\kappa.\mathrm{inter}\,s)$, and `hσ₁`, `hσ₂` pin it down as the canonical one: on $1 \otimes x$ it is the pullback of $x$ along $\mathrm{pullback.fst}$ restricted to $\mathcal{U}_\kappa.\mathrm{inter}\,s$, and on $a \otimes 1$ it is the $k$-algebra structure map coming from $\mathrm{pullback.snd}$.
--
--   **Tangent coordinates of a pair.** For a $B$-algebra $C$, two morphisms $u, v : \operatorname{Spec} C \to Y$, a morphism $x_k : A_k \to \operatorname{Spec} k$ with relative group law $L_k$, a morphism $a_k : A_k \to Y$, an open $U_e \subseteq A_k$ and a function $c$ from $\Gamma(A_k, U_e)$ to $\mathrm{Hom}_k(V^\vee, k \otimes_B C)$, the predicate [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt I V ι C u v x_k L_k a_k U_e c`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) asserts the existence of morphisms $w_0 : \operatorname{Spec} T \to A_k$, where $T := (k \otimes_B C) \otimes_k (k \oplus V)$ is the trivial-square-zero thickening, and $w_1 : \operatorname{Spec} T \to U_e$, with $w_0$ lying over the canonical base morphism $\operatorname{Spec} T \to \operatorname{Spec} k$, such that: $w_0$ followed by $a_k$ is a tangent vector of the pair $(u,v)$ in the sense of `IsTangentOfPair` (it factors as $\operatorname{Spec}$ of a Schlessinger map out of the pair ring of $I$ and $C$, composed with a morphism $\operatorname{Spec}(\mathrm{pairRing}\,I\,C) \to Y$ restricting to $u$ and $v$ along the two projections); $w_1$ followed by the inclusion $U_e \hookrightarrow A_k$ is the translate of $w_0$ by the inverse of the unit of $L_k$; and $c$ is the tangent-coordinate function attached to the ring homomorphism $\Gamma(A_k, U_e) \to T$ induced by $w_1$.
--
--   **The given cocycle $c$.** With $\Gamma(X_\kappa, \mathcal{U}_\kappa.U\,i_0)$ a $k$-algebra via $\mathrm{pullback.snd}$, $c$ is an element of $\mathrm{Algebra.PointDerivations}$ over $k$ of $\Gamma(X_\kappa, \mathcal{U}_\kappa.U\,i_0)$ at the evaluation homomorphism determined by $e_1$, with values in $\mathrm{Hom}_k\bigl(V^\vee, C^1(\mathcal{U}_\kappa, \mathcal{O})\bigr)$: that is, a $k$-linear map $a \mapsto c(a)$ satisfying the Leibniz rule $c(ab) = \mathrm{ev}(a)\,c(b) + \mathrm{ev}(b)\,c(a)$, where $C^1$ denotes the degree-$1$ Čech cochains of the $\mathcal{O}$-module presheaf $\mathrm{OModulePresheaf.unit}$ of $\mathrm{pullback.snd}$ on the cover $\mathcal{U}_\kappa$. The hypothesis `hc` states that every value $c(a)(\xi)$ lies in the kernel of the degree-$1$ Čech differential $d$ of that presheaf, i.e. is a $1$-cocycle.
--
--   **The re-gluing.** For each $1$-simplex $s$, $\tau\,s$ is a self-isomorphism of the scheme $\mathcal{U}.\mathrm{inter}\,s$, and $D$ is a second bare deformation of $(f_1, L_1)$ over $B$ with `hD : D₀.IsRegluingBy 𝒰 τ D`: each $\tau_s$ commutes with the structure morphism to $\operatorname{Spec} B$ and with the restriction of $D_0.g$ to $\mathcal{U}.\mathrm{inter}\,s$, and there are open immersions $\iota_i : \mathcal{U}.U\,i \to D.A$ over $\operatorname{Spec} B$, jointly surjective on points, compatible with $D_0.g$ and $D.g$, and satisfying the gluing identity: on $\mathcal{U}.\mathrm{inter}\,s$ the inclusion into $\mathcal{U}.U\,(s_0)$ followed by $\iota_{s_0}$ equals $\tau_s$ followed by the inclusion into $\mathcal{U}.U\,(s_1)$ followed by $\iota_{s_1}$. The hypothesis `hτ` states that for each $1$-simplex $s$ there is a function $c_s$ from $\Gamma(X_\kappa, \mathcal{U}_\kappa.U\,i_0)$ to $\mathrm{Hom}_k(V^\vee, k \otimes_B \Gamma(D_0.A, \mathcal{U}.\mathrm{inter}\,s))$ which is a tangent-coordinate system, in the above sense, for the pair consisting of the canonical morphism $\operatorname{Spec} \Gamma(D_0.A, \mathcal{U}.\mathrm{inter}\,s) \to D_0.A$ and of the same morphism twisted by $\tau_s$, taken with $x_k = \mathrm{pullback.snd}$, $L_k$ the base-changed group law, $a_k = \mathrm{pullback.fst}$ and $U_e = \mathcal{U}_\kappa.U\,i_0$, and which, after transport by $\sigma\,s$, is the $s$-component of $c$.
--
--   **The endomorphism and its local lifts.** $\varphi_1 : A_1 \to A_1$ is a morphism over $\operatorname{Spec} B_1$ (`hφ₁`); $j_\kappa : X_\kappa \to A_1$ satisfies $j_\kappa$ followed by $D_0.g$ equal to $\mathrm{pullback.fst}$ (`hjκ`); $\psi : X_\kappa \to X_\kappa$ is a morphism over $\operatorname{Spec} k$ (`hψ`) with $\psi$ followed by $j_\kappa$ equal to $j_\kappa$ followed by $\varphi_1$ (`hψ₁`). For each index $i$, $m_i : \mathcal{U}.U\,i \to D.A$ is a morphism over $\operatorname{Spec} B$, in the sense that $m_i$ followed by $D.f$ equals the open inclusion followed by $D_0.f$ (`hmpf`), and lifting $\varphi_1$ in the sense that the restriction of $D_0.g$ over $\mathcal{U}.U\,i$ followed by $m_i$ equals the inclusion of $D_0.g^{-1}(\mathcal{U}.U\,i)$ followed by $\varphi_1$ followed by $D.g$ (`hmpμ`).
--
--   **The twisted obstruction cochain.** $c'$ is, like $c$, an element of $\mathrm{Algebra.PointDerivations}$ over $k$ of $\Gamma(X_\kappa, \mathcal{U}_\kappa.U\,i_0)$ at the evaluation homomorphism given by $e_1$, with values in $\mathrm{Hom}_k\bigl(V^\vee, C^1(\mathcal{U}_\kappa,\mathcal{O})\bigr)$. The hypothesis `hc'` is the $\tau$-twisted clause: for each $1$-simplex $s$ there is a function $c_s$ from $\Gamma(X_\kappa, \mathcal{U}_\kappa.U\,i_0)$ to $\mathrm{Hom}_k(V^\vee, k \otimes_B \Gamma(D_0.A, \mathcal{U}.\mathrm{inter}\,s))$ which is a tangent-coordinate system for the pair of morphisms $\operatorname{Spec} \Gamma(D_0.A, \mathcal{U}.\mathrm{inter}\,s) \to D.A$ given by the inverse of the canonical isomorphism to the affine open followed by the inclusion $\mathcal{U}.\mathrm{inter}\,s \subseteq \mathcal{U}.U\,(s_0)$ and $m_{s_0}$, respectively by the inverse of that isomorphism followed by $\tau_s$, the inclusion $\mathcal{U}.\mathrm{inter}\,s \subseteq \mathcal{U}.U\,(s_1)$ and $m_{s_1}$, taken with $x_k = \mathrm{pullback.snd}$, $L_k$ the base-changed group law, $a_k = j_\kappa$ followed by $D.g$, and $U_e = \mathcal{U}_\kappa.U\,i_0$; and, after transport by $\sigma\,s$, $c_s$ is the $s$-component of $c'$.
--
--   **Conclusion.** For every $a \in \Gamma(X_\kappa, \mathcal{U}_\kappa.U\,i_0)$ and every $\xi \in V^\vee = \mathrm{Hom}_k(V,k)$, the degree-$1$ Čech differential of the $\mathcal{O}$-module presheaf $\mathrm{OModulePresheaf.unit}$ of $\mathrm{pullback.snd}$, on the cover $\mathcal{U}_\kappa$, annihilates the $1$-cochain $c'(a)(\xi)$: it equals $0$ in the degree-$2$ cochains.
--
--   This is the cocycle property of the obstruction cochain measuring the failure of the local lifts $m_i$ of the endomorphism $\varphi_1$ to a re-glued deformation $D$ to agree on the overlaps, the discrepancies being recorded in the $\tau$-twisted tangent coordinates of pairs of points with values in $k \otimes_B \mathcal{O}$. It is used in the criterion [`GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare), which decides when local lifts can be glued to a global endomorphism of the re-glued deformation in terms of the vanishing of a Čech class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare
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

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ : ψ ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)

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
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c'.1 a ξ) = 0 := by sorry
