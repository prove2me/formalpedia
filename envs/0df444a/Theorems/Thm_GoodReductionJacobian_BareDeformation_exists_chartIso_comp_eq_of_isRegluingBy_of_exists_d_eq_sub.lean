-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_chartIso_comp_eq_of_isRegluingBy_of_exists_d_eq_sub
-- name    : GoodReductionJacobian.BareDeformation.exists_chartIso_comp_eq_of_isRegluingBy_of_exists_d_eq_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/92bcdbf3-eca9-542a-9404-c97fcf7ed85f
-- title:
--   Cohomologous tangent cocycles give compatible chart automorphisms
-- statement:
--   The data are the following. Two rings $B$ and $B_1$ in `Type` (so `Scheme.{0}`), with $B$ a commutative Artinian local ring and $B_1$ a commutative $B$-algebra; write $I = \ker(B \to B_1)$ and $\mathfrak m =$ `maximalIdeal B`, and $k =$ `ResidueField B`. The hypotheses on this extension are: `hπ`, that $B \to B_1$ is surjective; `hker`, that $I$ is nilpotent; `hsmall`, that $I \cdot \mathfrak m = \bot$; and `hI`, that $I \le \mathfrak m$. Over $B_1$ there is a scheme $A_1$ with structure morphism $f_1 \colon A_1 \to \operatorname{Spec} B_1$ and a relative group law $L_1$ on $f_1$ (a functorial group structure on the sets `SchemeHomOver t f₁` of $T$-points over $\operatorname{Spec} B_1$, natural in $T$).
--
--   The ideal $I$ is presented by a module: $V$ is a finite-dimensional $k$-vector space, equipped also with a $B$-module structure compatible with the one through $k$ and with a right $k$-action agreeing with the left one, and $\iota \colon V \to_{B} B$ is an injective $B$-linear map (`hι`) whose range is $I$ viewed as a $B$-submodule (`hιI`).
--
--   Next, $D_0$ is a `BareDeformation f₁ L₁ B`: a scheme $D_0.A$ with a morphism $D_0.f \colon D_0.A \to \operatorname{Spec} B$, a commutative relative group law $D_0.L$ on $D_0.f$, the property bundle `AbelianSchemePropertyBundle` for $D_0.f$ (smooth, proper, connected fibres, and a relative group law exists), and a morphism $D_0.g \colon A_1 \to D_0.A$ making $A_1$ the base change of $D_0.A$ along $B \to B_1$ and compatible with the group laws. It is assumed that $D_0.f$ is separated. Further, $\mathcal U$ is an `OrderedAffineCover` of $D_0.A$: a finite linearly ordered index type $\mathcal U.\iota$ together with affine opens $\mathcal U.U\,i$ whose supremum is $\top$. For $s \in \mathcal U.\mathrm{Idx}\,1$, i.e. a strictly increasing pair $s \colon \mathrm{Fin}\,2 \to \mathcal U.\iota$, $\mathcal U.\mathrm{inter}\,s$ is the intersection of the two corresponding opens. A chart index $i_0$ is fixed, together with a section $e_0 \colon \operatorname{Spec} B \to \mathcal U.U\,i_0$ with $e_0$ followed by the open immersion equal to the unit section of $D_0.L$ at the identity (`he₀`), and, on the special fibre, a section $e_1 \colon \operatorname{Spec} k \to (\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$ with $e_1$ followed by the open immersion equal to the unit section of the base-changed group law `RelativeGroupLaw.baseChange (specMap B k) D₀.L` (`he₁`). Here $\mathcal U.\mathrm{baseChange}\,D_0.f\,k$ is the cover of the pullback $D_0.A \times_{\operatorname{Spec} B} \operatorname{Spec} k$ obtained by pulling back $\mathcal U$ along `pullback.fst`.
--
--   The overlaps of the special fibre are identified with base changes: $\sigma$ assigns to every $s$ a ring isomorphism $k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(D_0.A \times \operatorname{Spec} k, (\mathcal U.\mathrm{baseChange}\,D_0.f\,k).\mathrm{inter}\,s)$, and the two hypotheses `hσ₁`, `hσ₂` fix $\sigma$ as the canonical such map: $\sigma_s(1 \otimes x)$ is the restriction to the base-changed overlap of the image of $x$ under `pullback.fst`, and $\sigma_s(a \otimes 1)$ is the image of $a \in k$ under the structure map of the base-changed overlap.
--
--   On the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$ of the special fibre there are two elements $c$ and $c'$ of [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9): $k$-linear maps from $\Gamma$ of that chart to the $k$-module $\mathrm{Hom}_k(V^\vee, \check C^1)$, satisfying the Leibniz rule with respect to the evaluation ring homomorphism determined by $e_1$; here $\check C^1$ is `(OModulePresheaf.unit (pullback.snd D₀.f (specMap B k))).cochain (𝒰.baseChange D₀.f k) 1`, the $1$-cochains of the structure presheaf of the special fibre regarded as a presheaf of $k$-modules, i.e. families of sections over the overlaps $(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).\mathrm{inter}\,s$. The hypotheses `hc` and `hc'` state that all values $c(a)(\xi)$, respectively $c'(a)(\xi)$, for $a$ a section on the chart and $\xi \in V^\vee$, lie in the kernel of the degree-$1$ differential `d` of that cochain complex, i.e. are cocycles.
--
--   Two families $\tau, \tau'$ of self-isomorphisms of the overlaps $\mathcal U.\mathrm{inter}\,s$ are given, and two bare deformations $D$, $D'$ of $(f_1, L_1)$ to $B$, with `hD : D₀.IsRegluingBy 𝒰 τ D` and `hD' : D₀.IsRegluingBy 𝒰 τ' D'`. The predicate `IsRegluingBy` asserts that each $\tau_s$ is a morphism over $D_0.f$ and fixes the restriction of $D_0.g$ to the overlap, and that there are open immersions $\mathcal U.U\,i \to D.A$ over $B$, jointly surjective on points, compatible with $D_0.g$, and such that for every $s$ the inclusion of $\mathcal U.\mathrm{inter}\,s$ into the chart of index $s(0)$ followed by its immersion equals $\tau_s$ followed by the inclusion into the chart of index $s(1)$ followed by its immersion.
--
--   The hypotheses `hτ` and `hτ'` say that $c$, respectively $c'$, computes the tangent coordinates of these regluings. Explicitly, for each $s$ there is a function $c_s$ from the sections on the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$ to $\mathrm{Hom}_k(V^\vee, k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ such that `IsTangentCoordsOfPairAt` holds for the ideal $I$, the presentation $(V,\iota)$, the ring $C = \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, the pair of morphisms $\operatorname{Spec} C \to D_0.A$ consisting of the canonical `fromSpec` of the affine overlap and of `isoSpec.inv` followed by $\tau_s$ followed by the open immersion, with special fibre structure map `pullback.snd`, base-changed group law, $a_k =$ `pullback.fst` and chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$, and $c_s$ as coordinate function; and moreover $\sigma_s(c_s(a)(\xi))$ equals the component at $s$ of the cocycle $c(a)(\xi)$, for all sections $a$ on the chart and all $\xi \in V^\vee$. `IsTangentCoordsOfPairAt` itself requires the existence of a morphism $w_0$ from the spectrum of the thickening $(k \otimes_B C) \otimes_k (k \oplus V)$ to the special fibre lying over the base point, a lift $w_1$ into the chart which is the group-law translate of $w_0$ to the unit, the pair of morphisms to be the pair attached to $w_0$ through a Schlessinger map of the pair ring of $I$ and $C$, and the coordinate function to be the one read off from the ring homomorphism induced by $w_1$ on the chart.
--
--   The last hypothesis `hcob` is a coboundary condition: for every section $a$ on the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$ and every $\xi \in V^\vee$ there exists a $0$-cochain $b$ with $d^0 b = c(a)(\xi) - c'(a)(\xi)$.
--
--   The conclusion asserts the existence of a family $\alpha$ of self-isomorphisms of the charts, $\alpha_i \colon \mathcal U.U\,i \cong \mathcal U.U\,i$, and a family $\alpha r$ of self-isomorphisms of the overlaps indexed by $s \in \mathcal U.\mathrm{Idx}\,1$ and $j \in \mathrm{Fin}\,2$, such that, conjunct by conjunct:
--
--   1. each $\alpha_i$ is a morphism over $B$: $\alpha_i$ followed by the open immersion of $\mathcal U.U\,i$ and by $D_0.f$ equals the open immersion followed by $D_0.f$;
--
--   2. each $\alpha_i$ is the identity on the $B_1$-part: the restriction $D_0.g \mid_{\mathcal U.U\,i}$ followed by $\alpha_i$ equals $D_0.g \mid_{\mathcal U.U\,i}$;
--
--   3. for every $s$ and every $j \in \mathrm{Fin}\,2$, the isomorphism $\alpha r_{s,j}$ followed by the inclusion $\mathcal U.\mathrm{inter}\,s \to \mathcal U.U\,(s(j))$ equals that inclusion followed by $\alpha_{s(j)}$, so that $\alpha r_{s,j}$ is the restriction of $\alpha_{s(j)}$ to the overlap;
--
--   4. for every $s$: $\alpha r_{s,0}$ followed by $\tau'_s$ equals $\tau_s$ followed by $\alpha r_{s,1}$.
--
--   This is the comparison step in the theory of regluings of a bare deformation along a small extension of Artinian local rings: when the tangent cocycles of two regluing data differ by a Čech coboundary, the charts admit automorphisms over the base, trivial modulo the ideal, which conjugate one family of transition isomorphisms into the other. It is used by [`GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_exists_d_eq_sub`](thm.html#GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_exists_d_eq_sub) and its variant `…_bare`, where these chart automorphisms are glued to an isomorphism between the two reglued deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_chartIso_comp_eq_of_isRegluingBy_of_exists_d_eq_sub.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing Scheme.TwoAffineOpenCover
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_chartIso_comp_eq_of_isRegluingBy_of_exists_d_eq_sub
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
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
    ∃ (α : ∀ i : 𝒰.ι, ((↑(𝒰.U i) : Scheme.{0}) ≅ ↑(𝒰.U i)))
      (αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s))),
      (∀ i : 𝒰.ι, (α i).hom ≫ (𝒰.U i).ι ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f) ∧
      (∀ i : 𝒰.ι, (D₀.g ∣_ 𝒰.U i) ≫ (α i).hom = D₀.g ∣_ 𝒰.U i) ∧
      (∀ (s : 𝒰.Idx 1) (j : Fin 2),
        (αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom) ∧
      (∀ s : 𝒰.Idx 1, (αr s 0).hom ≫ (τ' s).hom = (τ s).hom ≫ (αr s 1).hom) := by sorry
