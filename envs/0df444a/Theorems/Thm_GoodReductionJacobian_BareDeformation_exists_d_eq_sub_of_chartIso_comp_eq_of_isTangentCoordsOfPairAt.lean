-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt
-- name    : GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/918561a2-bbed-50df-ad48-d6a1b9bc0936
-- title:
--   Compatible chart automorphisms make the two tangent cocycles cohomologous
-- statement:
--   The setting is a small extension of Artinian local base rings. Let $B$ be an Artinian local ring and $B_1$ a $B$-algebra; the hypotheses `hπ`, `hker`, `hsmall` and `hI` require that $\operatorname{algebraMap} B B_1$ be surjective, that its kernel $I = \ker(B \to B_1)$ be a nilpotent ideal, that $I \cdot \mathfrak m_B = \bot$, and that $I \le \mathfrak m_B$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $B_1$ carrying a relative group law $L_1$ (a functorial group structure on $T$-points over $\operatorname{Spec} B_1$, natural in $T$).
--
--   The kernel $I$ is presented as a module over the residue field: $V$ is a finite-dimensional $\operatorname{ResidueField} B$-module, also a $B$-module compatibly with the residue map and with a central right action, and $\iota : V \to_{\ell[B]} B$ is a $B$-linear map which by `hι` is injective and by `hιI` has range exactly $I$ viewed as a $B$-submodule of $B$.
--
--   Let $D_0$ be a bare deformation of $(f_1, L_1)$ over $B$: a scheme $D_0.A$ with structure morphism $D_0.f : D_0.A \to \operatorname{Spec} B$, a commutative relative group law $D_0.L$, an abelian-scheme property bundle for $D_0.f$, and a morphism $D_0.g : A_1 \to D_0.A$ exhibiting $f_1$ as the base change of $D_0.f$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the two group laws. The morphism $D_0.f$ is assumed separated.
--
--   Cover and base-point data: $\mathcal U$ is an ordered affine cover of $D_0.A$, that is, a finite linearly ordered index type together with affine opens $\mathcal U.U\,i$ whose supremum is $\top$; for $i \in \mathbb N$, $\mathcal U.\mathrm{Idx}\,i$ is the set of strictly monotone maps $\mathrm{Fin}(i+1) \to \mathcal U.\iota$ and $\mathcal U.\mathrm{inter}\,s = \bigwedge_j \mathcal U.U\,(s_j)$, so that $\mathcal U.\mathrm{Idx}\,1$ indexes the ordered pairs of indices and their pairwise intersections. A distinguished index $i_0$ is fixed, together with a morphism $e_0 : \operatorname{Spec} B \to \mathcal U.U\,i_0$ whose composite with the open immersion is, by `he₀`, the unit section of $D_0.L$; and a morphism $e_1 : \operatorname{Spec}(\operatorname{ResidueField} B) \to (\mathcal U.\mathrm{baseChange}\,D_0.f\,(\operatorname{ResidueField} B)).U\,i_0$ whose composite with the open immersion is, by `he₁`, the unit section of the base-changed group law $\mathrm{RelativeGroupLaw.baseChange}$ on the special fibre $\mathrm{pullback}\,D_0.f\,(\mathrm{specMap}\,B\,(\operatorname{ResidueField} B))$. Here $\mathcal U.\mathrm{baseChange}$ is the cover of the special fibre obtained by taking preimages of the $\mathcal U.U\,i$ along the first projection.
--
--   Comparison of sections on overlaps: for each $s \in \mathcal U.\mathrm{Idx}\,1$, $\sigma\,s$ is a ring isomorphism $\operatorname{ResidueField} B \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(\text{special fibre}, (\mathcal U.\mathrm{baseChange}\,\ldots).\mathrm{inter}\,s)$, required by `hσ₁` to send $1 \otimes x$ to the restriction to the base-changed overlap of the pullback of $x$ along the first projection, and by `hσ₂` to send $a \otimes 1$ to the image of $a$ under the structure algebra map of the special fibre.
--
--   The two cocycles: $c$ and $c'$ are elements of $\mathrm{Algebra.PointDerivations}$ of the $\operatorname{ResidueField} B$-algebra $\Gamma(\text{special fibre}, (\mathcal U.\mathrm{baseChange}\,\ldots).U\,i_0)$ at the evaluation homomorphism induced by $e_1$ (the composite of the inverse of the top isomorphism, $e_1$ on global sections and the $\Gamma$–$\operatorname{Spec}$ isomorphism), with values in the module of $\operatorname{ResidueField} B$-linear maps from $\mathrm{Module.Dual}(\operatorname{ResidueField} B)\,V$ to the group of $1$-cochains $\mathrm{cochain}\,(\mathcal U.\mathrm{baseChange}\,\ldots)\,1$ of the presheaf $\mathrm{OModulePresheaf.unit}$ of the second projection, i.e. of the structure sheaf of the special fibre; thus $c$ and $c'$ are $\operatorname{ResidueField} B$-linear maps satisfying the Leibniz rule at that point. By `hc` and `hc'`, for all sections $a$ and all $\xi$ in the dual of $V$, the $1$-cochains $c\,a\,\xi$ and $c'\,a\,\xi$ lie in the kernel of the Čech differential $d^1$, that is, they are $1$-cocycles.
--
--   The two regluings: $\tau$ and $\tau'$ assign to each $s \in \mathcal U.\mathrm{Idx}\,1$ a self-isomorphism of the scheme $\mathcal U.\mathrm{inter}\,s$, and $D$, $D'$ are bare deformations of $(f_1, L_1)$ over $B$ with $D_0.\mathrm{IsRegluingBy}\,\mathcal U\,\tau\,D$ and $D_0.\mathrm{IsRegluingBy}\,\mathcal U\,\tau'\,D'$. The predicate $\mathrm{IsRegluingBy}$ asserts that each $\tau\,s$ is a morphism over $\operatorname{Spec} B$ and is the identity after restriction along $D_0.g$, and that there are open immersions $\mathcal U.U\,i \to D.A$ over $\operatorname{Spec} B$ whose images cover $D.A$, compatible with $D_0.g$, and satisfying on each overlap the gluing identity $\mathrm{homOfLE} \text{ followed by the } (s_0)\text{-chart} = \tau\,s$ followed by $\mathrm{homOfLE}$ followed by the $(s_1)$-chart.
--
--   The hypotheses `hτ` and `hτ'` identify $c$ and $c'$ as the tangent coordinates of these regluings: for each $s \in \mathcal U.\mathrm{Idx}\,1$ there exists a family $c_s$ of $\operatorname{ResidueField} B$-linear maps from the dual of $V$ to $\operatorname{ResidueField} B \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, indexed by sections over the base-changed chart $U\,i_0$, such that $\mathrm{IsTangentCoordsOfPairAt}$ holds for the ideal $I$, the module $V$ with $\iota$, the ring $C = \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, the pair of morphisms $u = \mathrm{fromSpec}$ of the affine overlap and $v = \mathrm{isoSpec}^{-1}$ followed by $\tau\,s$ (respectively $\tau'\,s$) followed by the open immersion, the special-fibre structure morphism and group law, the first projection as the chart morphism, and the open $U\,i_0$ of the base-changed cover; by definition this says that there are a morphism $w_0$ from the spectrum of the thickening $(\operatorname{ResidueField} B \otimes_B C) \otimes_{\operatorname{ResidueField} B} \mathrm{TrivSqZeroExt}(\operatorname{ResidueField} B)\,V$ to the special fibre over the relative tangent base, and a morphism $w_1$ into $U\,i_0$, such that $w_0$ followed by the chart morphism is a tangent vector of the pair $(u, v)$ in the sense of $\mathrm{IsTangentOfPair}$ (it factors through a Schlessinger map out of the pair ring of $I$ and $C$), such that $w_1$ followed by the open immersion is the translate of $w_0$ by the group law into the unit section, and such that $c_s$ is the family $\mathrm{tangentCoords}$ attached to the induced ring homomorphism $\Gamma \to \text{thickening}$ of $w_1$. In addition, for all $a$ and $\xi$, $\sigma\,s\,(c_s\,a\,\xi)$ equals the $s$-component of $c\,a\,\xi$ in `hτ`, and of $c'\,a\,\xi$ in `hτ'`.
--
--   The intertwining data: $\alpha$ assigns to each index $i$ a self-isomorphism of the scheme $\mathcal U.U\,i$, with `hαf` requiring $\alpha\,i$ followed by the open immersion and $D_0.f$ to equal the open immersion followed by $D_0.f$, and `hαg` requiring $(D_0.g \mid_{\mathcal U.U\,i})$ followed by $\alpha\,i$ to equal $D_0.g \mid_{\mathcal U.U\,i}$. Further, $\alpha^r$ assigns to each $s \in \mathcal U.\mathrm{Idx}\,1$ and each $j \in \mathrm{Fin}\,2$ a self-isomorphism of $\mathcal U.\mathrm{inter}\,s$, with `hαr` requiring $(\alpha^r\,s\,j)$ followed by the restriction morphism $\mathrm{homOfLE}$ to equal $\mathrm{homOfLE}$ followed by $\alpha\,(s_j)$; and `hcomm` requires $(\alpha^r\,s\,0)$ followed by $\tau'\,s$ to equal $\tau\,s$ followed by $(\alpha^r\,s\,1)$.
--
--   Under these hypotheses the conclusion is: for every section $a \in \Gamma(\text{special fibre}, (\mathcal U.\mathrm{baseChange}\,D_0.f\,(\operatorname{ResidueField} B)).U\,i_0)$ and every $\xi$ in the dual of $V$ there exists a $0$-cochain $b$ of $\mathrm{OModulePresheaf.unit}$ for the base-changed cover with
--   $$d^0 b = c\,a\,\xi - c'\,a\,\xi.$$
--   That is, the two $1$-cocycles attached to the regluing data $\tau$ and $\tau'$ differ by a coboundary.
--
--   This is the converse half of the comparison of regluings of a bare deformation in the deformation-theoretic (Schlessinger-type) analysis of the special fibre: chart automorphisms over $B$ that are trivial modulo the small ideal and intertwine the two transition families force the corresponding Čech $1$-cocycles of tangent coordinates to be cohomologous. It is used by the statements [`GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt`](thm.html#GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt) and [`GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_isIso_of_isTangentCoordsOfPairAt_bare), which pass from an isomorphism of the reglued deformations to this cohomological relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_d_eq_sub_of_chartIso_comp_eq_of_isTangentCoordsOfPairAt
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
    (α : ∀ i : 𝒰.ι, ((↑(𝒰.U i) : Scheme.{0}) ≅ ↑(𝒰.U i)))
    (hαf : ∀ i : 𝒰.ι, (α i).hom ≫ (𝒰.U i).ι ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hαg : ∀ i : 𝒰.ι, (D₀.g ∣_ 𝒰.U i) ≫ (α i).hom = D₀.g ∣_ 𝒰.U i)
    (αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hαr : ∀ (s : 𝒰.Idx 1) (j : Fin 2),
      (αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom)
    (hcomm : ∀ s : 𝒰.Idx 1, (αr s 0).hom ≫ (τ' s).hom = (τ s).hom ≫ (αr s 1).hom) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 0,
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0 b =
          (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
          - (c' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ := by sorry
