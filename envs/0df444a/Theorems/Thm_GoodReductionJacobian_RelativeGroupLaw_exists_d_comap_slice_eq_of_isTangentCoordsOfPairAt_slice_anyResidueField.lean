-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/e3007650-77dd-563b-9466-7069e7831a40
-- title:
--   Restrictions of the obstruction cochain along unit slices are coboundaries
-- statement:
--   Throughout, $\kappa$ denotes the residue field $\mathrm{ResidueField}\,T'$ of $T'$, and for a morphism to an affine base the section rings $\Gamma(X,U)$ are regarded as algebras over the base ring via the structure morphism (`algebraOfHom`).
--
--   **Coefficients.** $T'$ is a commutative local Artinian ring and $T$ a commutative ring, with a ring homomorphism $\pi : T' \to T$ subject to: surjectivity (`hπ`), nilpotence of $\ker\pi$ (`hker`), $\ker\pi\cdot\mathfrak m_{T'} = 0$ (`hsmall`), and $\ker\pi \subseteq \mathfrak m_{T'}$ (`hI`). Furthermore $\rho : T \to \kappa$ is a ring homomorphism with $\rho\circ\pi$ the residue map of $T'$ (`hρ`).
--
--   **Tangent module.** $V$ is a $\kappa$-vector space of finite dimension, carrying in addition a $T'$-module structure compatible with the $\kappa$-structure and a central right $\kappa$-action, and $\iota : V \to T'$ is a $T'$-linear map that is injective (`hι`) and whose range, restricted to scalars in $T'$, is exactly $\ker\pi$ (`hιI`).
--
--   **Abelian scheme over $T$ and its lift over $T'$.** $f_0 : A_0 \to \operatorname{Spec} T$ carries a relative group law $L_0$, i.e. for every $T$-scheme $t : S \to \operatorname{Spec} T$ a group structure (multiplication, unit, inverse, associativity, unit laws, left inverse) on the set of morphisms $S \to A_0$ over $t$, natural with respect to morphisms of $T$-schemes; `hc₀` says this group law is commutative, and `h₀` is the bundle of properties asserting that $f_0$ is smooth and proper, that every fibre of $f_0$ is connected, and that $f_0$ admits a relative group law. Over $T'$ there is $f : A \to \operatorname{Spec} T'$, smooth (`hs`) and proper (`hp`), a morphism $g : A_0 \to A$ exhibiting $A_0$ as the pullback of $A$ along $\operatorname{Spec}$ of $\pi$ (`hg`), and a section $e$ of $f$, that is a morphism $e.1 : \operatorname{Spec} T' \to A$ with $e.1$ followed by $f$ the identity; `he` requires that $\operatorname{Spec}$ of $\pi$ followed by $e.1$ equal the unit section of $L_0$ followed by $g$.
--
--   **Cover of $P = A\times_{T'}A$ and local lifts of the multiplication.** The structure morphism of $P$ (first projection followed by $f$) is separated. $\mathcal W$ is an ordered affine cover of $P$: a finite linearly ordered index set, affine opens $U_i$ whose supremum is $P$. For a strictly increasing $s : \{0,\dots,n\} \to \mathcal W.\iota$ write $W_s = \bigcap_j U_{s(j)}$. There are morphisms $m_i : U_i \to A$ over $\operatorname{Spec} T'$ (`hmf`: $m_i$ followed by $f$ is the inclusion of $U_i$ followed by the structure morphism of $P$), and `hmμ` requires that along the canonical morphism $\nu : A_0\times_T A_0 \to P$ assembled from the two projections followed by $g$, the restriction of $\nu$ to $U_i$ followed by $m_i$ coincides with the inclusion of $\nu^{-1}U_i$ followed by the $L_0$-multiplication of the two projections of $A_0\times_T A_0$ followed by $g$; thus the $m_i$ are local lifts of $g\circ\mu_0$.
--
--   **Special fibre.** $f_k : A_k \to \operatorname{Spec}\kappa$ carries a relative group law $L_k$, and $i_0 : A_k \to A_0$ exhibits $A_k$ as the pullback of $A_0$ along $\operatorname{Spec}$ of $\rho$ (`hi₀`). $U_e$ is an open of $A_k$, affine (`hUe`), together with $e_1 : \operatorname{Spec}\kappa \to U_e$ whose composite with the inclusion of $U_e$ is the unit section of $L_k$ (`he₁`). Next, $b_k : P_k \to P$ is an affine morphism and $y_k : P_k \to \operatorname{Spec}\kappa$, with `hbk` exhibiting $(b_k, y_k)$ as the pullback of the structure morphism of $P$ along $\operatorname{Spec}$ of the residue map; $\sigma$ is a family, indexed by $n$ and by strictly increasing $s$, of ring isomorphisms $\kappa\otimes_{T'}\Gamma(P, W_s) \cong \Gamma(P_k, \bigcap_j b_k^{-1}U_{s(j)})$, normalised by `hσ₁` ($\sigma_s(1\otimes x)$ is the restriction of $b_k^\sharp x$) and `hσ₂` ($\sigma_s(a\otimes 1)$ is the image of $a$ under the $\kappa$-algebra structure map). Morphisms $p_1, p_2 : P_k \to A_k$ satisfy $p_i$ followed by $i_0$ followed by $g$ equals $b_k$ followed by the $i$-th projection of $P$ (`hp₁`, `hp₂`), are morphisms over $\kappa$ with value $y_k$ (`hp₁k`, `hp₂k`), and exhibit $P_k$ as $A_k\times_\kappa A_k$ (`hPk`). Further $e_k : \operatorname{Spec}\kappa \to A_k$ satisfies `hek` ($e_k$ followed by $i_0$ followed by $g$ equals $\operatorname{Spec}$ of the residue map followed by $e.1$) and `hekk` ($e_k$ followed by $f_k$ is the identity). Finally $i_X, i_Y : A_k \to P_k$ are closed immersions playing the roles of the two unit slices: $i_X$ followed by $p_1$ is the identity and $i_X$ followed by $p_2$ is $f_k$ followed by $e_k$ (`hiX₁`, `hiX₂`), with `hiXP` identifying $i_X$ followed by $b_k$ with $i_0$ followed by $g$ followed by the morphism $\langle \mathrm{id}_A,\, f\text{ followed by } e.1\rangle : A \to P$; symmetrically $i_Y$ followed by $p_1$ is $f_k$ followed by $e_k$, $i_Y$ followed by $p_2$ is the identity (`hiY₁`, `hiY₂`), and `hiYP` identifies $i_Y$ followed by $b_k$ with $i_0$ followed by $g$ followed by $\langle f\text{ followed by } e.1,\, \mathrm{id}_A\rangle$.
--
--   **The cochain $c$.** Let $\mathrm{ev} : \Gamma(A_k, U_e) \to \kappa$ be the ring homomorphism obtained from $e_1$ (the inverse of the top isomorphism of $U_e$, followed by the global-sections map of $e_1$, followed by the $\Gamma$–$\operatorname{Spec}$ isomorphism), i.e. evaluation at the unit point. Then $c$ is an element of the $\kappa$-submodule of $\mathrm{ev}$-derivations: a $\kappa$-linear map
--   $$c : \Gamma(A_k,U_e) \longrightarrow \mathrm{Hom}_\kappa\bigl(V^\vee,\ \check C^1(b_k^{-1}\mathcal W,\ \mathcal O_{P_k})\bigr)$$
--   with $c(ab) = \mathrm{ev}(a)\,c(b) + \mathrm{ev}(b)\,c(a)$, where the target degree-$1$ cochains for the unit $\mathcal O$-module presheaf of the structure morphism $p_1$ followed by $f_k$ assign to each strictly increasing pair $t$ a section over $\bigcap_j b_k^{-1}U_{t(j)}$.
--
--   **Compatibility `hc`.** For every pair $s$ (index in degree $1$) there is a map $c_s : \Gamma(A_k,U_e) \to \mathrm{Hom}_\kappa(V^\vee, \kappa\otimes_{T'}\Gamma(P,W_s))$ such that, first, $c_s$ is a system of tangent coordinates of the pair at the unit for the ideal $\ker\pi$, the module $V$, $\iota$ and the ring $C = \Gamma(P, W_s)$, relative to the two morphisms $\operatorname{Spec} C \to A$ obtained from the inverse of the affine isomorphism of $W_s$ followed by the inclusion $W_s \subseteq U_{s(0)}$ followed by $m_{s(0)}$, respectively with $s(1)$ in place of $s(0)$, and to the data $f_k$, $L_k$, $i_0$ followed by $g$, $U_e$; unfolded, `IsTangentCoordsOfPairAt` asserts the existence of a morphism $w_0$ from $\operatorname{Spec}$ of the thickening $(\kappa\otimes_{T'}C)\otimes_\kappa \mathrm{TrivSqZeroExt}(\kappa,V)$ to $A_k$ lying over the canonical base morphism, and of $w_1$ from that $\operatorname{Spec}$ to $U_e$, such that $w_0$ followed by $i_0$ followed by $g$ is a tangent vector of the given pair (i.e. factors through $\operatorname{Spec}$ of the pair ring of $\ker\pi$ and $C$, whose two structural maps recover the two morphisms, along a Schlessinger map into the thickening), such that $w_1$ followed by the inclusion of $U_e$ is the $L_k$-translate of $w_0$ to the unit, and such that $c_s$ is the tangent-coordinate function of the chart ring homomorphism attached to $w_1$. Second, $\sigma_s(c_s(a)(\xi)) = c(a)(\xi)_s$ for all $a \in \Gamma(A_k,U_e)$ and $\xi \in V^\vee$.
--
--   **The two unit slices.** $s_X, s_Y : A \to P$ are fixed by `hsX`, `hsY` to be $\langle\mathrm{id}_A,\, f\text{ followed by } e.1\rangle$ and $\langle f\text{ followed by } e.1,\, \mathrm{id}_A\rangle$. The hypothesis `hbX` requires, for every index $i$ and every proof that $s_X^{-1}U_i$ is affine, two things about $C = \Gamma(A, s_X^{-1}U_i)$: that the canonical morphism $\operatorname{Spec} C \to A$ and the composite (inverse of the affine isomorphism of $s_X^{-1}U_i$, followed by the restriction of $s_X$ to $U_i$, followed by $m_i$) become equal after composition with $\operatorname{Spec}$ of the quotient map of $C$ by the ideal generated by $\ker\pi$; and that this pair admits a system $b$ of tangent coordinates at the unit in the above sense, for $\ker\pi$, $V$, $\iota$, $C$ and the data $f_k$, $L_k$, $i_0$ followed by $g$, $U_e$. The hypothesis `hbY` is the same statement with $s_Y$ in place of $s_X$.
--
--   **Conclusion.** The conclusion is a conjunction of two assertions of identical shape.
--
--   (i) For all $a \in \Gamma(A_k, U_e)$ and all $\xi \in V^\vee$ there exists a degree-$0$ cochain $b$ for the unit $\mathcal O$-module presheaf of $f_k$ on the cover $(\mathcal W.\mathrm{comap}\, b_k).\mathrm{comap}\, i_X$ of $A_k$ — that is, a family of sections of $\mathcal O_{A_k}$ over the opens $i_X^{-1}b_k^{-1}U_i$ — whose Čech differential $d^0 b$ equals the degree-$1$ cochain sending each strictly increasing pair $t$ to the restriction, along the inclusion $\bigcap_j i_X^{-1}b_k^{-1}U_{t(j)} \subseteq i_X^{-1}\bigl(\bigcap_j b_k^{-1}U_{t(j)}\bigr)$, of the image under the section map of $i_X$ of the component $c(a)(\xi)_t$.
--
--   (ii) The same statement with $i_Y$ in place of $i_X$: for all $a$ and $\xi$ there is a degree-$0$ cochain $b$ on the cover $(\mathcal W.\mathrm{comap}\, b_k).\mathrm{comap}\, i_Y$ with $d^0 b$ equal to the pullback of $c(a)(\xi)$ along $i_Y$, restricted componentwise as above.
--
--   In the construction of a relative group law on a smooth proper lift $A$ of an abelian scheme over a small extension $T' \to T$, the local lifts $m_i$ of the multiplication on the cover $\mathcal W$ of $A\times_{T'}A$ differ on overlaps by a $1$-cochain with values in the tangent module, encoded by $c$; this statement records that the two restrictions of that cochain along the unit slices $(\mathrm{id}, e)$ and $(e, \mathrm{id})$ are Čech coboundaries on the special fibre. It feeds into [`GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle_anyResidueField`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle_anyResidueField), where the normalisation of the obstruction class along the unit sections is carried out.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
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
