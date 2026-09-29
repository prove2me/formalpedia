-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_d_eq_unitPullback_hom_obstruction_cocycle_sub_of_isRegluingBy_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_d_eq_unitPullback_hom_obstruction_cocycle_sub_of_isRegluingBy_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/fae0f1bb-bbc2-577a-8e9d-f19c8f6c485e
-- title:
--   Four-term re-gluing identity for the endomorphism obstruction cocycle
-- statement:
--   Throughout, $\kappa := \mathrm{ResidueField}\,B$ denotes the residue field of $B$, $I := \ker(B \to B_1)$, and $X := \mathrm{pullback}\,D_0.f\,(\mathrm{specMap}\,B\,\kappa)$ denotes the special fibre of $D_0.A$, with projections $p := \mathrm{pullback.fst}$ to $D_0.A$ and $\pi := \mathrm{pullback.snd}$ to $\operatorname{Spec}\kappa$. For an ordered affine cover the notation $\mathcal U_\kappa := \mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa$ is the cover of $X$ with the same index type whose members are the preimages $p^{-1}(\mathcal U.U\,i)$, and $\check C^n$ denotes the degree-$n$ cochains `(OModulePresheaf.unit π).cochain` of an ordered affine cover, i.e. families of sections of $\mathcal O_X$ over the intersections $\mathcal U.\mathrm{inter}\,s$ indexed by strictly increasing $(n+1)$-tuples $s$, with differential `d`.
--
--   *Coefficient data.* $B$ is a local artinian commutative ring with algebraically closed residue field and $B_1$ a commutative $B$-algebra such that `algebraMap B B₁` is surjective (`hπ`), its kernel $I$ is nilpotent (`hker`), satisfies $I\cdot\mathfrak m_B = 0$ (`hsmall`) and $I \subseteq \mathfrak m_B$ (`hI`). Further, $f_1 : A_1 \to \operatorname{Spec}B_1$ carries a relative group law $L_1$ which is commutative (`hc₁`) and for which `AbelianSchemePropertyBundle B₁ f₁` holds (`h₁`: $f_1$ smooth and proper with connected fibres and admitting a relative group law). Finally $V$ is a finite-dimensional $\kappa$-vector space, also a $B$-module compatibly with the $\kappa$-structure and with central right $\kappa$-action, and $\iota : V \to B$ is an injective $B$-linear map (`hι`) whose range is exactly $I$ viewed as a $B$-submodule of $B$ (`hιI`); thus $V \cong I$.
--
--   *The deformation $D_0$ and its cover.* $D_0$ is a `BareDeformation` of $(f_1, L_1)$ over $B$: a scheme $D_0.A$ with structure morphism $D_0.f$ to $\operatorname{Spec}B$, a commutative relative group law $D_0.L$, the abelian-scheme property bundle, and a morphism $D_0.g : A_1 \to D_0.A$ making $A_1$ the base change of $D_0.A$ along $\operatorname{Spec}B_1 \to \operatorname{Spec}B$ and compatible with the two group laws; $D_0.f$ is separated. $\mathcal U$ is a finite ordered affine cover of $D_0.A$, $i_0$ one of its indices, and $e_0$ a morphism $\operatorname{Spec}B \to \mathcal U.U\,i_0$ factoring the unit section of $D_0.L$ (`he₀`); likewise $e_1$ factors the unit section of the base-changed group law $\mathrm{RelativeGroupLaw.baseChange}$ through $\mathcal U_\kappa.U\,i_0$ (`he₁`). For each index $s$ of a strictly increasing pair, $\sigma_s$ is a ring isomorphism $\kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(X, \mathcal U_\kappa.\mathrm{inter}\,s)$ which on elements $1 \otimes x$ is the canonical base-change map composed with restriction (`hσ₁`) and on elements $a \otimes 1$ is the structure map of $\kappa$ (`hσ₂`).
--
--   *The re-gluing class $c$.* $c$ lies in $\mathrm{Algebra.PointDerivations}\,\kappa\,\Gamma(X, \mathcal U_\kappa.U\,i_0)\,\mathrm{ev}\,M$, with $\mathrm{ev}$ the evaluation ring homomorphism $\Gamma(X, \mathcal U_\kappa.U\,i_0) \to \kappa$ attached to $e_1$ and $M := \mathrm{Hom}_\kappa(V^\vee, \check C^1(\mathcal U_\kappa))$: that is, $c$ is a $\kappa$-linear map satisfying $c(ab) = \mathrm{ev}(a)\,c(b) + \mathrm{ev}(b)\,c(a)$. The hypothesis `hc` says that for all $a$ and all $\xi \in V^\vee$ the $1$-cochain $c(a)(\xi)$ is a cocycle, i.e. lies in the kernel of the degree-one differential of $\mathcal U_\kappa$.
--
--   *The re-glued deformation.* $\tau$ assigns to each strictly increasing pair $s$ a self-isomorphism of the scheme $\mathcal U.\mathrm{inter}\,s$, and $D$ is a second bare deformation with `hD : D₀.IsRegluingBy 𝒰 τ D`, which asserts: each $\tau_s$ is compatible with $D_0.f$ and with the restriction of $D_0.g$; and there are open immersions $\iota_i : \mathcal U.U\,i \to D.A$ over $\operatorname{Spec}B$ whose images cover $D.A$, compatible with $D_0.g$ and $D.g$, and satisfying the gluing identity $\mathrm{homOfLE} \cdot \iota_{s(0)} = \tau_s$ followed by $\mathrm{homOfLE} \cdot \iota_{s(1)}$ on $\mathcal U.\mathrm{inter}\,s$. The hypothesis `hτ` identifies $c$ with the tangent coordinates of the re-gluing: for each $s$ there are functions $c_s$ from $\Gamma(X, \mathcal U_\kappa.U\,i_0)$ to $\mathrm{Hom}_\kappa(V^\vee, \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ satisfying the predicate [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) for $I$, $V$, $\iota$, $C := \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, the pair of morphisms $\operatorname{Spec}C \to D_0.A$ given by `fromSpec` and by $\mathrm{isoSpec}^{-1}$ followed by $\tau_s$ and the inclusion, with $\pi$, the base-changed group law, $p$ and the chart $\mathcal U_\kappa.U\,i_0$ — that is, there exist a point $w_0$ of $D_0.A$ with values in the thickening $(\kappa \otimes_B C) \otimes_\kappa \mathrm{TrivSqZeroExt}\,\kappa\,V$ over the base, exhibiting the difference of the two morphisms as a tangent vector in the sense of `IsTangentOfPair`, and a lift $w_1$ into the chart of its translate by the group law, such that $c_s$ is the tangent-coordinate function of the induced ring homomorphism $\Gamma(X, \mathcal U_\kappa.U\,i_0) \to$ thickening; and moreover $\sigma_s(c_s(a)(\xi))$ is the $s$-component of $c(a)(\xi)$ for all $a, \xi$.
--
--   *Tangent-space presentation.* `hU` records that $\mathcal U_\kappa.U\,i_0$ is an affine open. $W$ is a $\kappa$-vector space and $\tau_W$ maps $W$ injectively (`hWinj`) into the morphisms $\operatorname{Spec}\kappa[\varepsilon] \to X$ over $\mathrm{tangentBase}$, with image exactly the set of $P$ satisfying `IsTangentVector` for the base-changed group law (`hWrange`: the zero section of $\kappa[\varepsilon]$ composed with $P$ is the unit point), additively (`hWadd`: $\tau_W(v+w)$ is the group-law product of $\tau_W v$ and $\tau_W w$) and compatibly with scalars (`hWsmul`: $\tau_W(a\cdot v)$ is $\mathrm{tangentScale}\,\kappa\,a$ followed by $\tau_W v$). $\Phi$ gives, for every $\kappa$-vector space $M$, a $\kappa$-linear isomorphism between the point derivations of $\Gamma(X, \mathcal U_\kappa.U\,i_0)$ at $\mathrm{ev}$ with values in $M$ and $W \otimes_\kappa M$, natural in $M$ (`hΦnat`: $\Phi$ intertwines [`Algebra.PointDerivations.map g`](def/Algebra_PointDerivations.html#L47) with $\mathrm{id}_W \otimes g$) and normalised by `hΦpin`: for a $\kappa$-valued point derivation $\delta$ and a ring homomorphism $\chi$ to the dual numbers whose first component is $\mathrm{ev}$ and whose second is $\delta$, the tangent vector $\tau_W$ of $\Phi(\kappa)(\delta)$ under $W \otimes_\kappa \kappa \cong W$ equals $\operatorname{Spec}\chi$ followed by `hU.fromSpec`.
--
--   *The endomorphism and its reduction.* $\varphi_1$ is an endomorphism of $A_1$ over $\operatorname{Spec}B_1$ (`hφ₁`), $j_\kappa : X \to A_1$ satisfies $j_\kappa$ followed by $D_0.g$ equal to $p$ (`hjκ`), and $\psi$ is an endomorphism of $X$ over $\operatorname{Spec}\kappa$ (`hψ`) with $\psi$ followed by $j_\kappa$ equal to $j_\kappa$ followed by $\varphi_1$ (`hψ₁`) and such that push-forward along $\psi$ is a homomorphism for the base-changed group law (`hψhom`). $\theta_\psi : W \to W$ is $\kappa$-linear with $\tau_W(\theta_\psi w) = \mathrm{pushPt}\,\psi\,(\tau_W w)$ (`hθψ`), the tangent map of $\psi$.
--
--   *Local lifts and their obstruction cochains.* $m_i : \mathcal U.U\,i \to D_0.A$ are morphisms over $\operatorname{Spec}B$ (`hmf`) lifting $\varphi_1$ through $D_0.g$ on the preimage of each chart (`hmμ`), and $c_0$ is a point derivation of the same type as $c$ such that (`hc₀`) for each $s$ the pair of charts $m_{s(0)}, m_{s(1)}$ on $\mathcal U.\mathrm{inter}\,s$ admits tangent coordinates in the sense of `IsTangentCoordsOfPairAt` (with $ak = p$) whose image under $\sigma_s$ is the $s$-component of $c_0$, and (`hc₀Z`) $c_0(a)(\xi)$ is a cocycle for all $a, \xi$. Similarly $mp_i : \mathcal U.U\,i \to D.A$ are morphisms with $mp_i$ followed by $D.f$ equal to the inclusion followed by $D_0.f$ (`hmpf`) and lifting $\varphi_1$ through $D.g$ (`hmpμ`), and $c'$ is a point derivation of the same type such that (`hc'`) for each $s$ the pair consisting of $mp_{s(0)}$ and of $\tau_s$ followed by $mp_{s(1)}$ admits tangent coordinates in the sense of `IsTangentCoordsOfPairAt`, now with the morphism $j_\kappa$ followed by $D.g$ in place of $p$, whose image under $\sigma_s$ is the $s$-component of $c'$.
--
--   *Conclusion.* There exist a finite ordered affine cover $\mathcal V_0$ of $X$, two index maps $\lambda_0, \lambda_0' : \mathcal V_0.\iota \to \mathcal U.\iota$, and proofs that $\mathcal V_0.U\,v \subseteq \psi^{-1}(\mathcal U_\kappa.U\,(\lambda_0 v))$ for all $v$ and $\mathcal V_0.U\,v \subseteq \mathrm{id}^{-1}(\mathcal U_\kappa.U\,(\lambda_0' v))$ for all $v$, such that for every section $a \in \Gamma(X, \mathcal U_\kappa.U\,i_0)$ and every $\xi \in V^\vee$ there is a $0$-cochain $b \in \check C^0(\mathcal V_0)$ with
--   $$d^0 b \;=\; P_{\mathrm{id}}\bigl(c'(a)(\xi)\bigr) \;-\; P_{\mathrm{id}}\bigl(c_0(a)(\xi)\bigr) \;-\; P_{\mathrm{id}}\bigl(c^\theta(a)(\xi)\bigr) \;+\; P_{\psi}\bigl(c(a)(\xi)\bigr).$$
--   Here $P_{\mathrm{id}} := \mathrm{OModulePresheaf.unitPullback}$ along the identity of $X$ from $\mathcal U_\kappa$ to $\mathcal V_0$ through $\lambda_0'$ in degree $1$, and $P_\psi$ is the corresponding pullback along $\psi$ through $\lambda_0$ in degree $1$; each sends a $1$-cochain $z$ to the cochain whose value at $s$ is, when $\lambda \circ s$ is injective, the sign of the sorting permutation times the restriction of the pullback of $z$ at the sorted index, and $0$ otherwise. The twisted class $c^\theta$ is $\Phi(M)^{-1}\bigl((\theta_\psi \otimes \mathrm{id}_M)(\Phi(M)(c))\bigr)$ for $M = \mathrm{Hom}_\kappa(V^\vee, \check C^1(\mathcal U_\kappa))$. Note the order of quantifiers: the cover and the index maps are uniform in $a$ and $\xi$, while the $0$-cochain $b$ may depend on them.
--
--   This is the comparison, after passage to a suitable refinement of the special-fibre cover, of the obstruction cochains governing the extension of an endomorphism $\varphi_1$ of $A_1$ to the two deformations $D_0$ and $D$, where $D$ is obtained from $D_0$ by re-gluing along the isomorphisms $\tau_s$ with associated class $c$: the difference of the two obstruction cocycles agrees, up to a Čech coboundary, with the $\theta_\psi$-twist of the re-gluing class minus its $\psi$-pullback. It is used in [`GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare), where the liftability of the endomorphism to a re-glued deformation is converted into the vanishing of a single cohomology class, and it relies on the existence of admissible refinements (`exists_orderedAffineCover_local_lifts_factor_bare`) together with the obstruction-comparison identity on a given cover (`exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_d_eq_unitPullback_hom_obstruction_cocycle_sub_of_isRegluingBy_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_d_eq_unitPullback_hom_obstruction_cocycle_sub_of_isRegluingBy_bare
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
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c'.1 a ξ s) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∃ (𝒱₀ : (pullback D₀.f (specMap B (ResidueField B))).OrderedAffineCover) (lam₀ lam₀' : 𝒱₀.ι → (𝒰.baseChange D₀.f (ResidueField B)).ι)
      (hl₀ : ∀ v, 𝒱₀.U v ≤ ψ ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀ v))
      (hl₀' : ∀ v, 𝒱₀.U v ≤ (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀' v)),
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain 𝒱₀ 0,
          (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d 𝒱₀ 0 b =
            OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱₀ (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c'.1 a ξ)
              - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱₀ (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ)
              - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱₀ (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c))).1 a ξ)
              + OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ 𝒱₀ (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c.1 a ξ) := by sorry
