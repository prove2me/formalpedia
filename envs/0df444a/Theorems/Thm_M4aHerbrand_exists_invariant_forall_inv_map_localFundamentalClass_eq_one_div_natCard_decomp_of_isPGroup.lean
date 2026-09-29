-- Prove2me | Theorems.Thm_M4aHerbrand_exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup
-- name    : M4aHerbrand.exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/62e244f4-02d6-55c2-9751-ed3f0427d3d2
-- title:
--   Invariant maps at a p-group layer with local value 1/|D_w|
-- statement:
--   Throughout, $E \subseteq F$ are number fields with $F/E$ Galois, $G = \mathrm{Gal}(F/E)$ written in Lean as `F ≃ₐ[E] F`, and $C_F = (\mathbb{A}_F)^\times / (\text{principal idèles})$ is the idèle class group `IdeleClassGroup (𝓞 F) F`. A datum $D$ of type `IdeleGaloisDescent (𝓞 F) E F` is fixed: a monoid homomorphism from $G$ to the ring automorphisms of the adele ring $\mathbb{A}_F$, compatible with the structure map $F \to \mathbb{A}_F$ in the sense that $D.\mathrm{act}\,g$ carries the image of $x \in F$ to the image of $g x$, each $D.\mathrm{act}\,g$ being continuous; it induces actions `D.unitsAct` on $(\mathbb{A}_F)^\times$ and `D.classAct` on $C_F$.
--
--   Hypotheses on the actions: $G$ acts on $(\mathbb{A}_F)^\times$ and on $C_F$ through multiplicative-distributive actions, and `hactI`, `hact` pin these actions to the descent datum, $g \bullet x = D.\mathrm{unitsAct}\,g\,x$ for units and $g \bullet c = D.\mathrm{classAct}\,g\,c$ for classes. Hypothesis on the infinite places, `hinf`: for every infinite place $v$ of $F$, any $g \in G$ lying in the stabiliser [`NumberField.InfPlaceDecomp.decomp E F v`](def/NumberField_ArchimedeanIdeleModule.html#L23) of $v$ equals $1$, i.e. all infinite decomposition groups are trivial. Hypothesis on the group: for a prime $p$, `hG` asserts that $G$ is a $p$-group.
--
--   Single-place data: for each finite place $w$ of $F$ (a point of `HeightOneSpectrum (𝓞 F)`) a group homomorphism $\iota_w \colon (F_w)^\times \to (\mathbb{A}_F)^\times$ is given, and `hι` pins its values: `finPart w (ι w x) = x`, `finPart w' (ι w x) = 1` for every finite place $w' \neq w$, and `infPart (ι w x) = 1`; that is, $\iota_w x$ is the idèle concentrated at $w$ with entry $x$. Further, for each $w$ a morphism $\lambda_w$ of representations of the decomposition group $D_w =$ [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) (the decomposition subgroup in $G$ of the valuation subring of $w$) is given, from the additive representation attached to $(F_w)^\times$ to the restriction to $D_w$ of the representation attached to $C_F$, and `hlam` pins its values: $\lambda_w$ sends the additive copy of $x \in (F_w)^\times$ to the additive copy of the class of $\iota_w x$ in $C_F$.
--
--   The conclusion asserts the existence of an additive homomorphism $\mathrm{inv}_G \colon H^2(G, C_F) \to \mathbb{Q}/\mathbb{Z}$ (the target being `AddCircle (1 : ℚ)`) and of a family $\mathrm{inv}_H \colon H^2(H, C_F) \to \mathbb{Q}/\mathbb{Z}$, indexed by all subgroups $H \le G$ and defined on the cohomology of the restriction of $C_F$ along $H \hookrightarrow G$, such that the following six conjuncts hold.
--
--   (i) $\mathrm{inv}_G$ is injective; (ii) each $\mathrm{inv}_H$ is injective; (iii) the range of $\mathrm{inv}_G$ consists exactly of the $t \in \mathbb{Q}/\mathbb{Z}$ with $\mathrm{Nat.card}\,G \cdot t = 0$; (iv) for every $H \le G$, the range of $\mathrm{inv}_H$ consists exactly of the $t$ with $\mathrm{Nat.card}\,H \cdot t = 0$; (v) for every $H \le G$ and every $x \in H^2(G, C_F)$, the restriction of $x$ to $H$ — the map induced on degree-$2$ cohomology by the inclusion $H \hookrightarrow G$ together with the identity of the restricted representation — satisfies $\mathrm{inv}_H(\mathrm{res}\,x) = [G : H] \cdot \mathrm{inv}_G(x)$.
--
--   (vi) The global sum formula, quantified over all auxiliary data. Given: a family of morphisms $\mathrm{pr}_w$ from the restriction to $D_w$ of $(\mathbb{A}_F)^\times$ to $(F_w)^\times$ whose values are pinned to `finPart w`; a morphism $\pi$ from $(\mathbb{A}_F)^\times$ to $C_F$ over $G$ whose values are pinned to the quotient map; a class $x \in H^2(G, (\mathbb{A}_F)^\times)$; a family of primes $q(v)$ indexed by the finite places $v$ of $E$; finite extensions $L'(v)$ of $\mathbb{Q}_{q(v)}$ inside `PadicAlgCl (q v)` carrying actions of the decomposition group $D_{w(v)}$ of the chosen place $w(v) =$ [`NumberField.PlaceAbove.above E F v`](def/NumberField_PlaceAbove.html#L27) above $v$, on $L'(v)$ as a semiring and on its units; ring isomorphisms $\Phi_v \colon F_{w(v)} \xrightarrow{\sim} L'(v)$; and the compatibility hypotheses that $D_{w(v)}$ acts trivially on the image of $\mathbb{Q}_{q(v)}$, that the action on units is induced by the action on $L'(v)$, and that $\Phi_v$ is $D_{w(v)}$-equivariant; base fields $K_0(v)$, finite over $\mathbb{Q}_{q(v)}$, with [`ExtCitation.LocalLevel.IsBase`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13), i.e. $K_0(v) \le L'(v)$ and an element of $L'(v)$ lies in $K_0(v)$ precisely when it is fixed by all of $D_{w(v)}$; morphisms $\theta_v$ of $D_{w(v)}$-representations from $(L'(v))^\times$ to $(F_{w(v)})^\times$ whose values are $\Phi_v^{-1}$ on underlying elements; classes $u'(v) \in H^2(D_{w(v)}, (L'(v))^\times)$ each satisfying [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) for the data $(q(v), L'(v), D_{w(v)}, K_0(v))$ — the condition that for every finite overfield $M \supseteq L'(v)$ with a finite group $H$ acting faithfully, normal subgroups $N_L, N_n \le H$, an isomorphism $e \colon D_{w(v)} \simeq H/N_L$, an element $\varphi \in H$ and a unit $\pi \in M^\times$ forming an `IsUnramOverlayerDatum` (trivial action on $\mathbb{Q}_{q(v)}$, compatibility of the unit action, $K_0(v)$ and $L'(v)$ cut out as the fixed fields of $H$ and of $N_L$, compatibility of the $D_{w(v)}$- and $H$-actions through $e$, $\#(H/N_n) = \#D_{w(v)}$ with $H/N_n$ generated by the image of $\varphi$, the Frobenius congruence for $\varphi$ on $N_n$-invariant integral elements, and $\pi$ an $H$-fixed element of $K_0(v)$ of norm $<1$ which is of maximal norm among $N_n$-invariant elements of norm $<1$), and for every equivariant lift $\iota$ of $(L'(v))^\times$ into $M^\times$, the image of $u'(v)$ under the induced map in degree $2$ equals the inflation from $H/N_n$ of the class of the explicit $2$-cocycle built by `carryFun` from the generator of $H/N_n$ and the uniformiser $\pi$; and finally integers $n(v)$ such that for every $v$ the image of $x$ under restriction to $D_{w(v)}$ followed by $\mathrm{pr}_{w(v)}$ equals $n(v)$ times the image of $u'(v)$ under $\theta_v$ in degree $2$. Then
--   $$\mathrm{inv}_G\big(\pi_*(x)\big) \;=\; \sum^{\mathrm{f}}_{v} \frac{n(v)}{\#D_{w(v)}} \quad \text{in } \mathbb{Q}/\mathbb{Z},$$
--   the sum being the finite sum `∑ᶠ` over all finite places $v$ of $E$.
--
--   (vii) The local normalisation at a single place. For every finite place $w$ of $F$, every prime $q$, every finite extension $L'$ of $\mathbb{Q}_q$ inside `PadicAlgCl q` with actions of $D_w$ on $L'$ and on $(L')^\times$, every ring isomorphism $\Phi \colon F_w \xrightarrow{\sim} L'$ subject to the same three compatibilities (triviality on $\mathbb{Q}_q$, coherence of the action on units, $D_w$-equivariance of $\Phi$), every base field $K_0$ finite over $\mathbb{Q}_q$ with `IsBase q L' D_w K₀`, every morphism $\theta$ of $D_w$-representations from $(L')^\times$ to $(F_w)^\times$ whose underlying values are given by $\Phi^{-1}$, and every $u' \in H^2(D_w, (L')^\times)$ satisfying `IsLocalFundamentalClass q L' D_w K₀`,
--   $$\mathrm{inv}_{D_w}\big((\lambda_w)_*\,\theta_*\,u'\big) \;=\; \frac{1}{\#D_w} \quad \text{in } \mathbb{Q}/\mathbb{Z},$$
--   where $\theta_*$ and $(\lambda_w)_*$ are the maps induced in degree $2$ over the identity of $D_w$.
--
--   This is Tate's reciprocity law for the idèle class formation at a finite layer whose Galois group is a $p$-group, in the form that also records the normalisation of the invariant map at a single finite place: the local fundamental class of $F_w/E_v$, pushed into $H^2(D_w, C_F)$ by the place-$w$ embedding of idèles, has invariant $1/\#D_w$. It is used by [`M4aHerbrand.exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two`](thm.html#M4aHerbrand.exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two) and by [`M4aHerbrand.exists_invariant_groupCohomology_ideleClassGroup_of_isPGroup_of_ne_two`](thm.html#M4aHerbrand.exists_invariant_groupCohomology_ideleClassGroup_of_isPGroup_of_ne_two), and derives from the sum-formula version [`M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup`](thm.html#M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup) together with the existence and uniqueness of local fundamental classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))

    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F)) :
    ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup (F ≃ₐ[E] F), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ)),

      Function.Injective invG ∧ (∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧
      (∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F)) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • invG x) ∧

      (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
            n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ∧

      (∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by sorry
