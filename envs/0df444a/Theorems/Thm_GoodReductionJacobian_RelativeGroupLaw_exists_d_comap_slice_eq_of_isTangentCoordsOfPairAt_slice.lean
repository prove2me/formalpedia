-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b6a50b73-042a-5eeb-ade5-375194dd7127
-- title:
--   Unit-slice restrictions of the obstruction cochain are coboundaries
-- statement:
--   Fix a commutative Artinian local ring $T'$ whose residue field $k = \mathrm{ResidueField}\,T'$ is algebraically closed, a commutative ring $T$, and a surjective ring homomorphism $\pi : T' \to T$ whose kernel $I = \ker \pi$ is nilpotent and satisfies $I \cdot \mathfrak m_{T'} = 0$ and $I \subseteq \mathfrak m_{T'}$.
--
--   *Data over $T$ and over $T'$.* A scheme $A_0$ with a morphism $f_0 : A_0 \to \operatorname{Spec} T$, a relative group law $L_0$ on $f_0$ (that is: functorial multiplication, unit and inverse on $T$-points over an arbitrary base, with associativity, the two unit laws, left inverses, and naturality of multiplication under base change), the hypothesis that $L_0$ is commutative, and the bundle `AbelianSchemePropertyBundle T f₀` asserting that $f_0$ is smooth and proper, that every fibre of $f_0$ is connected, and that $f_0$ carries a relative group law. Further, a scheme $A$ with a smooth and proper morphism $f : A \to \operatorname{Spec} T'$, a morphism $g : A_0 \to A$ exhibiting $A_0$ as the base change of $A$ along $\operatorname{Spec}(\pi)$, and a section $e$ of $f$ (an element of `SchemeHomOver (𝟙 (Spec T')) f`, i.e. a morphism $e_1 : \operatorname{Spec} T' \to A$ with $e_1 \circ f = \mathrm{id}$) whose base change along $\pi$ is the unit section of $L_0$ followed by $g$.
--
--   *Linear data for the kernel.* A ring homomorphism $\rho : T \to k$ with $\rho \circ \pi = \mathrm{residue}_{T'}$; a $k$-vector space $V$ of finite dimension, carried also as a $T'$-module compatibly with the scalar tower and with central $k^{\mathrm{op}}$-action; and an injective $T'$-linear map $\iota : V \to T'$ whose range is $I$ viewed as a $T'$-submodule. Thus $V$ identifies the kernel of the small extension with a finite-dimensional $k$-vector space.
--
--   *Covering and local lifts of the multiplication.* The structure morphism $\mathrm{pr}_1 \circ f$ of $P = A \times_{T'} A$ is assumed separated, and $\mathcal W$ is an ordered affine cover of $P$ (a finite linearly ordered index set $\mathcal W.\iota$ together with affine opens $\mathcal W.U_i$ whose supremum is $\top$). For each $i$ a morphism $m_i : \mathcal W.U_i \to A$ is given, subject to: `hmf`, that $m_i$ followed by $f$ is the open immersion of $\mathcal W.U_i$ followed by the structure morphism of $P$; and `hmμ`, that the restriction of the canonical morphism $A_0 \times_T A_0 \to P$ (the lift of $\mathrm{pr}_1 \circ g$ and $\mathrm{pr}_2 \circ g$) to $\mathcal W.U_i$, followed by $m_i$, coincides with the inclusion of the preimage open followed by the multiplication $L_0.\mathrm{mul}$ of the two projections of $A_0 \times_T A_0$ and then $g$. So the $m_i$ are local lifts to $A$ of the multiplication of $A_0$ composed with $g$.
--
--   *Special fibres.* A scheme $A_k$ with $f_k : A_k \to \operatorname{Spec} k$, a relative group law $L_k$ on $f_k$, and $i_0 : A_k \to A_0$ exhibiting $A_k$ as the base change of $A_0$ along $\operatorname{Spec}(\rho)$; an affine open $U_e \subseteq A_k$ together with $e_1 : \operatorname{Spec} k \to U_e$ whose composite with the open immersion is the unit section of $L_k$. Also a scheme $P_k$ with an affine morphism $b_k : P_k \to P$ and $y_k : P_k \to \operatorname{Spec} k$ exhibiting $P_k$ as the base change of $P$ along $\operatorname{Spec}(\mathrm{residue}_{T'})$, and, for every $n$ and every strictly increasing $(n+1)$-tuple $s$ of indices, a ring isomorphism $\sigma_s : k \otimes_{T'} \Gamma(P, \mathcal W.\mathrm{inter}\,s) \to \Gamma(P_k, (\mathcal W.\mathrm{comap}\,b_k).\mathrm{inter}\,s)$ between the base change of the sections over the intersection $\bigcap_j \mathcal W.U_{s(j)}$ and the sections of $P_k$ over the corresponding intersection of the pulled-back cover; the hypotheses `hσ₁` and `hσ₂` require that $\sigma_s(1 \otimes x)$ is the pullback $b_k^\ast x$ restricted to that intersection, and that $\sigma_s(a \otimes 1)$ is the image of $a$ under the structure map of $\Gamma(P_k, \cdot)$ as a $k$-algebra.
--
--   *Projections and slices on the special fibre.* Morphisms $p_1, p_2 : P_k \to A_k$ with $p_j \circ (i_0 \circ g)$ equal to $b_k$ followed by the $j$-th projection of $P$, with $p_j \circ f_k = y_k$, and such that $(p_1, p_2)$ exhibits $P_k$ as $A_k \times_k A_k$; a unit section $e_k : \operatorname{Spec} k \to A_k$ of $f_k$ whose composite with $i_0 \circ g$ is the reduction of $e_1$; and two closed immersions $i_X, i_Y : A_k \to P_k$ with $i_X \circ p_1 = \mathrm{id}$, $i_X \circ p_2 = f_k \circ e_k$ and $i_X \circ b_k = (i_0 \circ g)$ followed by the lift $(\mathrm{id}_A, f \circ e_1)$, and symmetrically $i_Y \circ p_1 = f_k \circ e_k$, $i_Y \circ p_2 = \mathrm{id}$, $i_Y \circ b_k = (i_0 \circ g)$ followed by $(f \circ e_1, \mathrm{id}_A)$; these are the two unit slices of $P_k$.
--
--   *The obstruction cochain $c$ and its local description.* The datum $c$ is an element of $\mathrm{PointDerivations}_k(\Gamma(A_k, U_e), \mathrm{ev}, M)$, where $\mathrm{ev} : \Gamma(A_k, U_e) \to k$ is evaluation at the unit obtained from $e_1$ and $M = \mathrm{Hom}_k(V^\ast, \check C^1(\mathcal W.\mathrm{comap}\,b_k, \mathcal O))$ with $V^\ast = \mathrm{Hom}_k(V,k)$ and $\check C^1$ the degree-$1$ cochains of the unit $\mathcal O$-module presheaf of $p_1 \circ f_k$ on the pulled-back cover; being a point derivation means $k$-linearity together with $c(ab) = \mathrm{ev}(a)\,c(b) + \mathrm{ev}(b)\,c(a)$. The hypothesis `hc` states that for every $s : \mathcal W.\mathrm{Idx}\,1$, i.e. every pair $i < j$ of indices, there is a map $c_s : \Gamma(A_k, U_e) \to \mathrm{Hom}_k(V^\ast, k \otimes_{T'} \Gamma(P, \mathcal W.\mathrm{inter}\,s))$ which is a family of tangent coordinates, in the sense of `IsTangentCoordsOfPairAt` for the ideal $I$, the space $V$ and the map $\iota$, of the pair of morphisms $\operatorname{Spec} \Gamma(P, \mathcal W.\mathrm{inter}\,s) \to A$ given by the inverse of the isospec isomorphism of the intersection followed by $\mathcal W.\mathrm{inter}\,s \le \mathcal W.U_{s(0)}$ and $m_{s(0)}$, respectively by $\mathcal W.\mathrm{inter}\,s \le \mathcal W.U_{s(1)}$ and $m_{s(1)}$, taken with respect to $f_k$, $L_k$, the morphism $i_0 \circ g$ and the chart $U_e$ — unfolded, this asks for a point $w_0$ of $A_k$ over the thickening ring $(k \otimes_{T'} C) \otimes_k (k \oplus V)$, $C = \Gamma(P, \mathcal W.\mathrm{inter}\,s)$, lying over the canonical base morphism, such that $w_0 \circ (i_0 \circ g)$ realises the pair in the sense of `IsTangentOfPair` (both morphisms factor through a single morphism out of $\operatorname{Spec}$ of the pair ring along its two projections, and $w_0 \circ (i_0 \circ g)$ is that morphism precomposed with a Schlessinger map), such that the $L_k$-translate of $w_0$ by the inverse of its zero-section value factors through $U_e$, and such that $c_s$ is the tangent-coordinate function of the resulting chart homomorphism. In addition `hc` demands $\sigma_s(c_s(a)(\xi)) = c(a)(\xi)_s$ for all $a$ and $\xi$, so that $c$ is the $k$-cochain induced by the local coordinate families.
--
--   *Slices and the hypotheses along them.* The morphisms $s_X, s_Y : A \to P$ are fixed by $s_X = (\mathrm{id}_A, f \circ e_1)$ and $s_Y = (f \circ e_1, \mathrm{id}_A)$. The hypothesis `hbX` requires, for every index $i$ and every proof that $s_X^{-1}(\mathcal W.U_i)$ is an affine open of $A$, two things: first, that the canonical morphism $\operatorname{Spec} \Gamma(A, s_X^{-1}\mathcal W.U_i) \to A$ and the morphism obtained from the isospec inverse followed by the restriction of $s_X$ and by $m_i$ agree after precomposition with $\operatorname{Spec}$ of the quotient by the ideal generated by $I$ in $\Gamma(A, s_X^{-1}\mathcal W.U_i)$, that is, agree modulo $I$; second, that this pair of morphisms admits a family of tangent coordinates $b$ with values in $\mathrm{Hom}_k(V^\ast, k \otimes_{T'} \Gamma(A, s_X^{-1}\mathcal W.U_i))$, in the same sense `IsTangentCoordsOfPairAt` relative to $f_k$, $L_k$, $i_0 \circ g$ and $U_e$. The hypothesis `hbY` is the same statement for $s_Y$.
--
--   *Conclusion.* Two assertions hold.
--
--   First, for every $a \in \Gamma(A_k, U_e)$ and every $\xi \in V^\ast$ there is a $0$-cochain $b$ of the unit $\mathcal O$-module presheaf of $f_k$ on the cover $(\mathcal W.\mathrm{comap}\,b_k).\mathrm{comap}\,i_X$ of $A_k$ whose Čech differential in degree $0$ is the $1$-cochain sending $t$ to the image of $c(a)(\xi)_t$ under $i_X^\ast$ on sections over $(\mathcal W.\mathrm{comap}\,b_k).\mathrm{inter}\,t$, restricted to the corresponding intersection of the twice pulled-back cover.
--
--   Second, the same assertion with $i_Y$ in place of $i_X$ throughout: for all $a$ and $\xi$ the pullback of the $1$-cochain $c(a)(\xi)$ along $i_Y$ is the Čech coboundary of a $0$-cochain on $(\mathcal W.\mathrm{comap}\,b_k).\mathrm{comap}\,i_Y$.
--
--   This is a step in the construction of a group law on a smooth proper lift $A$ of an abelian scheme $A_0$ across a small extension $T' \to T$: the local lifts $m_i$ of the multiplication differ on overlaps by a Čech $1$-cochain with coefficients in the tangent sheaf twisted by $V$, recorded here as the point derivation $c$, and the statement says that the restriction of this cochain to each of the two unit slices of $A_k \times_k A_k$ is a coboundary. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle), and relies on the comparison results [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat), [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add) and [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated (pullback.fst f f ≫ f)]
    (𝒲 : (pullback f f).OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f)
    (hmμ : ∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g)

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    {Pk : Scheme.{u}} (bk : Pk ⟶ pullback f f) [IsAffineHom bk] (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(pullback f f, 𝒲.inter s)),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(pullback f f, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)

    (p₁ p₂ : Pk ⟶ Ak)
    (hp₁ : p₁ ≫ i₀ ≫ g = bk ≫ pullback.fst f f) (hp₁k : p₁ ≫ fk = yk)
    (hp₂ : p₂ ≫ i₀ ≫ g = bk ≫ pullback.snd f f) (hp₂k : p₂ ≫ fk = yk)
    (hPk : IsPullback p₁ p₂ fk fk)
    (ek : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak)
    (hek : ek ≫ i₀ ≫ g = Spec.map (CommRingCat.ofHom (residue T')) ≫ e.1) (hekk : ek ≫ fk = 𝟙 _)
    (iX : Ak ⟶ Pk) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 Ak) (hiX₂ : iX ≫ p₂ = fk ≫ ek)
    (hiXP : iX ≫ bk = (i₀ ≫ g) ≫ pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (iY : Ak ⟶ Pk) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fk ≫ ek) (hiY₂ : iY ≫ p₂ = 𝟙 Ak)
    (hiYP : iY ≫ bk = (i₀ ≫ g) ≫ pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (c : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 1)))
    (hc : letI := algebraOfHom fk Ue
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
        ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk Lk (i₀ ≫ g) Ue cs ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s))

    (sX : A ⟶ pullback f f) (hsX : sX = pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (sY : A ⟶ pullback f f) (hsY : sY = pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))

    (hbX : ∀ (i : 𝒲.ι) (hU : IsAffineOpen (sX ⁻¹ᵁ 𝒲.U i)),
      letI := algebraOfHom f (sX ⁻¹ᵁ 𝒲.U i)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sX ⁻¹ᵁ 𝒲.U i))))) ≫ hU.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sX ⁻¹ᵁ 𝒲.U i))))) ≫
            (hU.isoSpec.inv ≫ (sX ∣_ 𝒲.U i) ≫ m i) ∧
      ∃ b : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, sX ⁻¹ᵁ 𝒲.U i))),
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, sX ⁻¹ᵁ 𝒲.U i)
          hU.fromSpec (hU.isoSpec.inv ≫ (sX ∣_ 𝒲.U i) ≫ m i) fk Lk (i₀ ≫ g) Ue b)
    (hbY : ∀ (i : 𝒲.ι) (hU : IsAffineOpen (sY ⁻¹ᵁ 𝒲.U i)),
      letI := algebraOfHom f (sY ⁻¹ᵁ 𝒲.U i)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sY ⁻¹ᵁ 𝒲.U i))))) ≫ hU.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sY ⁻¹ᵁ 𝒲.U i))))) ≫
            (hU.isoSpec.inv ≫ (sY ∣_ 𝒲.U i) ≫ m i) ∧
      ∃ b : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, sY ⁻¹ᵁ 𝒲.U i))),
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, sY ⁻¹ᵁ 𝒲.U i)
          hU.fromSpec (hU.isoSpec.inv ≫ (sY ∣_ 𝒲.U i) ≫ m i) fk Lk (i₀ ≫ g) Ue b) :
    (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iX) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iX) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iX t)).op).hom
              ((iX.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) ∧
    (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iY) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iY) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iY t)).op).hom
              ((iY.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) := by sorry
