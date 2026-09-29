-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/89d7df47-9d65-5be2-a7c0-2314cf0cdb8a
-- title:
--   Regluing law: four-term obstruction combination is a coboundary
-- statement:
--   Throughout, write $\kappa$ for the residue field of $B$, $I$ for the kernel of $B \to B_1$, $X_\kappa$ for the pullback of $D_0.f$ along $\operatorname{Spec}\kappa \to \operatorname{Spec}B$, $p_\kappa$ and $\pi_\kappa$ for the two projections of that pullback, $L_\kappa$ for the base change of $D_0.L$ along $\operatorname{Spec}\kappa \to \operatorname{Spec}B$, and, for an ordered affine cover $\mathcal W$ of $D_0.A$, $\mathcal W_\kappa$ for the cover of $X_\kappa$ by the preimages under $p_\kappa$ of the members of $\mathcal W$. Čech cochains are taken for the $\mathcal O$-module presheaf `OModulePresheaf.unit` of $\pi_\kappa$, whose sections over an open are the ring of sections there; a cochain of degree $n$ assigns to every strictly increasing $(n+1)$-tuple $s$ of indices a section over the intersection of the corresponding charts, and $d$ denotes the associated differential.
--
--   **Coefficient data.** $B$ is a local artinian ring with algebraically closed residue field, $B_1$ a $B$-algebra such that the structure map is surjective (`hπ`), its kernel $I$ is nilpotent (`hker`), satisfies $I\cdot\mathfrak m_B = 0$ (`hsmall`) and $I \subseteq \mathfrak m_B$ (`hI`). Further, $f_1 : A_1 \to \operatorname{Spec}B_1$ carries a relative group law $L_1$, assumed commutative (`hc₁`), and `h₁` asserts the property bundle for $f_1$ over $B_1$: smoothness, properness, connected fibres, and existence of a relative group law. The module $V$ is a finite-dimensional $\kappa$-vector space, also a $B$-module compatibly, and $\iota : V \to B$ is an injective $B$-linear map (`hι`) whose image is $I$ viewed as a $B$-submodule (`hιI`).
--
--   **The deformation $D_0$ and its cover.** $D_0$ is a bare deformation of $(f_1,L_1)$ to $B$: a scheme $D_0.A$ with a morphism $D_0.f$ to $\operatorname{Spec}B$, a commutative relative group law $D_0.L$, the abelian-scheme property bundle over $B$, and a morphism $D_0.g : A_1 \to D_0.A$ making $(D_0.g, f_1, D_0.f, \operatorname{Spec}(B\to B_1))$ a pullback square and compatible with the two group laws; $D_0.f$ is separated. $\mathcal U$ is a finite ordered affine cover of $D_0.A$ with a distinguished index $i_0$, and $e_0$ is a morphism $\operatorname{Spec}B \to \mathcal U.U\,i_0$ which, followed by the inclusion of that chart, is the unit section of $D_0.L$ (`he₀`); likewise $e_1$ is a morphism $\operatorname{Spec}\kappa \to (\mathcal U_\kappa).U\,i_0$ which, followed by the inclusion, is the unit section of $L_\kappa$ (`he₁`), and `hU` asserts that $(\mathcal U_\kappa).U\,i_0$ is affine. The family $\sigma$ gives, for every $1$-simplex $s$ of $\mathcal U$, a ring isomorphism $\kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(X_\kappa, (\mathcal U_\kappa).\mathrm{inter}\,s)$, and `hσ₁`, `hσ₂` pin it down as the canonical base-change isomorphism: on $1 \otimes x$ it is $p_\kappa^{\ast}x$ restricted to the base-changed intersection, and on $a \otimes 1$ it is the structure map of $\kappa$.
--
--   **Tangent coordinates of a pair.** For a $B$-algebra $C$, two morphisms $u, v : \operatorname{Spec}C \to Y$, a $\kappa$-scheme $A_k \to \operatorname{Spec}\kappa$ with relative group law $L_k$, a morphism $ak : A_k \to Y$, an open $Ue \subseteq A_k$ and a family $c : \Gamma(A_k,Ue) \to (\operatorname{Hom}_\kappa(V,\kappa) \to_\kappa \kappa\otimes_B C)$, the predicate `IsTangentCoordsOfPairAt I V ι C u v` asserts the existence of a morphism $w_0$ from the spectrum of the thickening $(\kappa\otimes_B C)\otimes_\kappa (\kappa \oplus V)$ to $A_k$ over the base, and of a morphism $w_1$ from that spectrum into $Ue$, such that $w_0$ followed by $ak$ witnesses `IsTangentOfPair I V ι C u v` (the pair $(u,v)$ is obtained from a morphism out of the spectrum of the pair ring of $I$ and $C$ via a Schlessinger map), such that $w_1$ followed by the inclusion of $Ue$ is the $L_k$-translate of $w_0$ to the unit section, and such that $c$ is the family of tangent coordinates of the ring homomorphism $\Gamma(A_k,Ue) \to$ thickening induced by $w_1$.
--
--   **The regluing class $c$.** $c$ is a point derivation of the chart ring $\Gamma(X_\kappa,(\mathcal U_\kappa).U\,i_0)$ over $\kappa$, at the evaluation homomorphism determined by $e_1$, with values in $M := \operatorname{Hom}_\kappa(V,\kappa) \to_\kappa \check C^1(\mathcal U_\kappa)$ — that is, a $\kappa$-linear map satisfying the Leibniz rule with respect to that evaluation. The hypothesis `hc` asserts that for every section $a$ of the chart and every $\xi \in \operatorname{Hom}_\kappa(V,\kappa)$ the $1$-cochain $c(a)(\xi)$ is a Čech cocycle, $d^1(c(a)(\xi)) = 0$.
--
--   **Regluing of $D_0$ into $D$.** $\tau$ assigns to every $1$-simplex $s$ of $\mathcal U$ a self-isomorphism of the intersection $\mathcal U.\mathrm{inter}\,s$; `hτB` says $\tau_s$ is a morphism over $\operatorname{Spec}B$ and `hτg` that it fixes $D_0.g$ restricted to that intersection. $D$ is a second bare deformation of $(f_1,L_1)$ to $B$, and the family $\iota D$ gives morphisms $\mathcal U.U\,i \to D.A$ which are open immersions (`hιopen`), are compatible with the structure morphisms (`hιf`), have jointly surjective underlying maps (`hιsurj`), are compatible with $D_0.g$ and $D.g$ (`hιg`), and glue along $\tau$: on each $1$-simplex $s$ the inclusion of the intersection followed by $\iota D_{s_0}$ equals $\tau_s$ followed by the inclusion into $\mathcal U.U\,s_1$ followed by $\iota D_{s_1}$ (`hιglue`). The hypothesis `hτ` expresses that $c$ records the regluing datum: for each $1$-simplex $s$ there is a family $cs$ of tangent coordinates, with $C = \Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$, for the pair consisting of the canonical $\operatorname{Spec}C$-point of the intersection and of that point composed with $\tau_s$, taken with respect to $\pi_\kappa$, $L_\kappa$, the morphism $p_\kappa$ and the chart $(\mathcal U_\kappa).U\,i_0$, and $\sigma_s(cs(a)(\xi))$ is the $s$-component of $c(a)(\xi)$ for all $a$, $\xi$.
--
--   **Tangent presentation.** $W$ is a $\kappa$-vector space and $\tau_W$ an injective map (`hWinj`) from $W$ to morphisms from the dual-number base $\operatorname{Spec}\kappa[\varepsilon]$ to $X_\kappa$ over $\pi_\kappa$, whose image consists exactly of the tangent vectors of $L_\kappa$, i.e. of those points whose restriction along the zero section is the unit (`hWrange`), which is additive for the group law $L_\kappa$ (`hWadd`) and homogeneous for the scaling of dual numbers (`hWsmul`). The family $\Phi$ gives, for every $\kappa$-vector space $M$, a $\kappa$-linear isomorphism from the point derivations of the chart ring at the unit with values in $M$ onto $W \otimes_\kappa M$; `hΦnat` asserts naturality in $M$, and `hΦpin` normalises $\Phi$: for a $\kappa$-valued point derivation $\delta$ and a ring homomorphism $\chi$ from the chart ring to $\kappa[\varepsilon]$ whose first component is the evaluation at the unit and whose second component is $\delta$, the tangent vector $\tau_W$ of the image of $\Phi(\kappa)\delta$ under $W\otimes_\kappa\kappa \cong W$ is $\operatorname{Spec}\chi$ followed by the canonical morphism of the affine chart.
--
--   **The endomorphism and its local lifts.** $\varphi_1$ is an endomorphism of $A_1$ over $\operatorname{Spec}B_1$ (`hφ₁`); $j\kappa : X_\kappa \to A_1$ satisfies $j\kappa$ followed by $D_0.g$ equal to $p_\kappa$ (`hjκ`); $\psi$ is an endomorphism of $X_\kappa$ over $\operatorname{Spec}\kappa$ (`hψ`) with $\psi$ followed by $j\kappa$ equal to $j\kappa$ followed by $\varphi_1$ (`hψ₁`), and `hψhom` says that composition with $\psi$ is a homomorphism for $L_\kappa$ on points over any base. The linear map $\theta_\psi$ on $W$ is the induced action on tangent vectors: $\tau_W(\theta_\psi w)$ is $\tau_W(w)$ pushed forward by $\psi$ (`hθψ`).
--
--   The family $m$ consists of morphisms $\mathcal U.U\,i \to D_0.A$ over $\operatorname{Spec}B$ (`hmf`) which lift $\varphi_1$ in the sense that the restriction of $D_0.g$ to the chart followed by $m_i$ equals the inclusion followed by $\varphi_1$ followed by $D_0.g$ (`hmμ`). The cochain-valued point derivation $c_0$ has values in $\operatorname{Hom}_\kappa(V,\kappa) \to_\kappa \check C^1(\mathcal U_\kappa)$, and `hc₀` states that for each $1$-simplex $s$ its $s$-component, transported through $\sigma_s$, is given by tangent coordinates for the pair of $\operatorname{Spec}\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$-points of $D_0.A$ obtained from $m_{s_0}$ and $m_{s_1}$ restricted to the intersection, relative to $\pi_\kappa$, $L_\kappa$, $p_\kappa$ and the chart $(\mathcal U_\kappa).U\,i_0$; `hc₀Z` states that $c_0(a)(\xi)$ is a Čech cocycle for all $a$, $\xi$.
--
--   Similarly $mp$ consists of morphisms $\mathcal U.U\,i \to D.A$ over $\operatorname{Spec}B$ (`hmpf`) lifting $\varphi_1$ to $D$ (`hmpμ`), and $c'$ is a cochain-valued point derivation such that, by `hc'`, for each $1$-simplex $s$ its $s$-component, transported through $\sigma_s$, is given by tangent coordinates for the pair of points of $D.A$ consisting of $mp_{s_0}$ restricted to the intersection and of $\tau_s$ followed by $mp_{s_1}$ restricted, taken with respect to $\pi_\kappa$, $L_\kappa$, the morphism $j\kappa$ followed by $D.g$, and the chart $(\mathcal U_\kappa).U\,i_0$.
--
--   **The refinement.** $\mathcal V$ is a further finite ordered affine cover of $D_0.A$, with index maps $\lambda_0,\lambda_0' : \mathcal V.\iota \to \mathcal U.\iota$ such that $\mathcal V.U\,v \subseteq \mathcal U.U(\lambda_0' v)$ (`hsub`), and with morphisms $n_v, n'_v : \mathcal V.U\,v \to \mathcal U.U(\lambda_0 v)$ factoring the local lifts: $n_v$ followed by the inclusion of $\mathcal U.U(\lambda_0 v)$ equals the inclusion $\mathcal V.U\,v \subseteq \mathcal U.U(\lambda_0' v)$ followed by $m_{\lambda_0' v}$ (`hn`), and $n'_v$ followed by $\iota D_{\lambda_0 v}$ equals that inclusion followed by $mp_{\lambda_0' v}$ (`hn'`). On the special fibre, $(\mathcal V_\kappa).U\,v$ is contained in the preimage under $\psi$ of $(\mathcal U_\kappa).U(\lambda_0 v)$ (`hl₀`) and in the preimage under the identity of $(\mathcal U_\kappa).U(\lambda_0' v)$ (`hl₀'`).
--
--   **Conclusion.** For every section $a$ of $\Gamma(X_\kappa,(\mathcal U_\kappa).U\,i_0)$ and every $\xi \in \operatorname{Hom}_\kappa(V,\kappa)$ there exists a Čech $0$-cochain $b$ for the cover $\mathcal V_\kappa$ with
--   $$d^0 b \;=\; P_{\mathrm{id}}\bigl(c'(a)(\xi)\bigr) \;-\; P_{\mathrm{id}}\bigl(c_0(a)(\xi)\bigr) \;-\; P_{\mathrm{id}}\bigl(c^{\theta}(a)(\xi)\bigr) \;+\; P_{\psi}\bigl(c(a)(\xi)\bigr),$$
--   where $c^{\theta} := \Phi(M)^{-1}\bigl((\theta_\psi \otimes \mathrm{id}_M)(\Phi(M)c)\bigr)$ with $M = \operatorname{Hom}_\kappa(V,\kappa) \to_\kappa \check C^1(\mathcal U_\kappa)$, where $P_{\mathrm{id}}$ denotes `OModulePresheaf.unitPullback` in degree $1$ along the identity of $X_\kappa$ with index map $\lambda_0'$ and the containments `hl₀'`, and $P_\psi$ denotes the same operation along $\psi$ with index map $\lambda_0$ and the containments `hl₀`: on a $1$-simplex $s$ of $\mathcal V_\kappa$ such a pullback is the sign of the sorting permutation of $\lambda \circ s$ times the restriction of the pullback of the value of the cochain at the sorted simplex, and is zero when $\lambda \circ s$ fails to be injective. Thus the four-term combination $P_{\mathrm{id}}c' - P_{\mathrm{id}}c_0 - P_{\mathrm{id}}c^{\theta} + P_{\psi}c$, evaluated at each $a$ and $\xi$, is a Čech coboundary on the refinement $\mathcal V_\kappa$.
--
--   This is the comparison law governing how the obstruction cochain to lifting the endomorphism $\varphi_1$ of the abelian scheme over $B_1$ changes when the deformation $D_0$ is reglued by the $1$-cochain $\tau$ with class $c$: the obstruction for the reglued deformation $D$ differs from that for $D_0$ by $\theta_\psi c - \psi^{*}c$ up to a coboundary on the given refinement. It is used by the statement that produces such a refinement, which in turn feeds the analysis of the endomorphism obstruction for bare deformations in a small extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare
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

    (𝒱 : D₀.A.OrderedAffineCover) (lam₀ lam₀' : 𝒱.ι → 𝒰.ι) (hsub : ∀ v, 𝒱.U v ≤ 𝒰.U (lam₀' v))
    (n n' : ∀ v : 𝒱.ι, (↑(𝒱.U v) : Scheme.{0}) ⟶ ↑(𝒰.U (lam₀ v)))
    (hn : ∀ v, n v ≫ (𝒰.U (lam₀ v)).ι = D₀.A.homOfLE (hsub v) ≫ m (lam₀' v))
    (hn' : ∀ v, n' v ≫ ιD (lam₀ v) = D₀.A.homOfLE (hsub v) ≫ mp (lam₀' v))
    (hl₀ : ∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤ ψ ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀ v))
    (hl₀' : ∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤
      (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀' v)) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒱.baseChange D₀.f (ResidueField B)) 0,
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒱.baseChange D₀.f (ResidueField B)) 0 b =
          OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c'.1 a ξ)
            - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ)
            - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c))).1 a ξ)
            + OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c.1 a ξ) := by sorry
