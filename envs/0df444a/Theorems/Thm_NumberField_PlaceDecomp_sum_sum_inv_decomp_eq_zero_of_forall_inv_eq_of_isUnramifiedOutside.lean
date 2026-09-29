-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside
-- name    : NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/ffd9ffb9-1e93-5e97-9a64-cb0f724e1357
-- title:
--   Vanishing of the sum of local invariants over S
-- statement:
--   Fix an odd prime $p$ (so $p \neq 2$) and a finite set $S$ of rational primes.
--
--   **Fields.** $F_0$ is an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ which is finite-dimensional and Galois over $\mathbb{Q}$ and a number field, and the hypothesis `hF₀` asserts `F₀.IsUnramifiedOutside S`: $F_0$ is finite-dimensional over $\mathbb{Q}$ and, for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup) is contained in the fixing subgroup of $F_0$. Further, $E_0$ is an intermediate field of $\mathbb{Q} \subseteq F_0$ which is a number field, and `hG` asserts that $G := F_0 \simeq_{\mathrm{alg}[E_0]} F_0$ is a $p$-group. For a finite place $w$ of $F_0$ (a height-one prime of $\mathcal{O}_{F_0}$), $D_w :=$ `decomp E₀ F₀ w` denotes the decomposition subgroup over $E_0$ of the valuation subring of the $w$-adic valuation on $F_0$.
--
--   **Idèle-class frame.** $D$ is an `IdeleGaloisDescent (𝓞 F₀) E₀ F₀`: a monoid homomorphism $g \mapsto D.\mathrm{act}(g)$ from $G$ to the ring automorphisms of the adèle ring of $F_0$, compatible with the structure map $F_0 \to \mathbb{A}_{F_0}$ and continuous for each $g$. Two unnamed hypotheses provide a `MulDistribMulAction` of $G$ on the idèle class group $\mathrm{C}_{F_0} = (\mathbb{A}_{F_0})^\times / \mathrm{principalIdeles}$ and assert that this action agrees with `D.classAct`, the map induced by $D.\mathrm{act}$ on classes. Next, $\iota$ assigns to each finite place $w$ a monoid homomorphism $(F_{0,w})^\times \to (\mathbb{A}_{F_0})^\times$, and an unnamed hypothesis states that $\iota_w$ produces idèles concentrated at $w$: $\mathrm{finPart}_w(\iota_w x) = x$, $\mathrm{finPart}_{w'}(\iota_w x) = 1$ for every $w' \neq w$, and $\mathrm{infPart}(\iota_w x) = 1$. The family $\mathrm{lam}$ assigns to each $w$ a morphism of $D_w$-representations from the multiplicative $D_w$-module $(F_{0,w})^\times$ to the restriction along $D_w \hookrightarrow G$ of the $G$-module $\mathrm{C}_{F_0}$, and an unnamed hypothesis identifies it on elements: $\mathrm{lam}_w$ sends (the additive avatar of) $x$ to the class of $\iota_w x$. The family $\rho$ assigns to each $w$ a morphism of $D_w$-representations from the restriction to $D_w$ of the $G$-module $F_0^\times$ to $(F_{0,w})^\times$, and an unnamed hypothesis identifies it as the map induced by the structure map $F_0 \to F_{0,w}$ on units. Finally, $V$ assigns to each $q \in S$ a finite set of finite places of $E_0$, characterised by the unnamed hypothesis $v \in V_q \iff q \in v$, i.e. $V_q$ is the set of places of $E_0$ above $q$.
--
--   **The class $x$.** $f$ is a function on pairs of automorphisms of $\overline{\mathbb{Q}}$ with values in $\mathbb{Z}/p$, and $\zeta_F \in F_0^\times$ satisfies $\zeta_F^p = 1$ (`hζp`). The function $b$ on pairs in $\mathrm{Gal}(F_0/\mathbb{Q})$ with values in the multiplicative $\mathrm{Gal}(F_0/\mathbb{Q})$-module $F_0^\times$ satisfies `hb`: whenever $\hat{g}, \hat{h}$ are automorphisms of $\overline{\mathbb{Q}}$ restricting to $g, h$ on $F_0$, one has $b(g,h) = \zeta_F^{\,\mathrm{val}(f(\hat{g},\hat{h}))}$; and `hbc` asserts that $b$ is a $2$-cocycle. The homomorphism $r : G \to \mathrm{Gal}(F_0/\mathbb{Q})$ satisfies `hr` ($r$ is the inclusion of Galois groups, $r(g)$ acting as $g$ on $F_0$), and $\varphi$ is a morphism from the restriction along $r$ of the $\mathrm{Gal}(F_0/\mathbb{Q})$-module $F_0^\times$ to the $G$-module $F_0^\times$, which `hφ` identifies with the identity on underlying units. The class $x \in H^2(G, F_0^\times)$ is required by `hx` to be the image of the cohomology class of $\langle b, \mathrm{hbc}\rangle$ under `groupCohomology.map r φ 2`.
--
--   **Invariant maps.** $\mathrm{invG}$ is an additive homomorphism from $H^2(G, \mathrm{C}_{F_0})$ to $\mathbb{Q}/\mathbb{Z}$ (`AddCircle (1 : ℚ)`), and $\mathrm{inv}$ assigns to each subgroup $H \leq G$ an additive homomorphism from $H^2(H, \mathrm{C}_{F_0})$, the cohomology of the restricted module, to $\mathbb{Q}/\mathbb{Z}$. Unnamed hypotheses require: $\mathrm{invG}$ is injective; each $\mathrm{inv}\,H$ is injective; the range of $\mathrm{invG}$ consists exactly of the $t$ with $\#G \cdot t = 0$; the range of $\mathrm{inv}\,H$ consists exactly of the $t$ with $\#H \cdot t = 0$; and the restriction formula $\mathrm{inv}\,H(\mathrm{res}_H\,y) = [G:H] \cdot \mathrm{invG}(y)$, where $\mathrm{res}_H$ is `groupCohomology.map H.subtype` applied to the identity of the restricted module. A further unnamed hypothesis is the local normalisation: for every finite place $w$ of $F_0$, every prime $q$, every finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying a multiplicative semiring action of $D_w$ and a `MulDistribMulAction` on $(L')^\times$, every ring isomorphism $\Phi : F_{0,w} \cong L'$, subject to the compatibilities that $D_w$ fixes the image of $\mathbb{Q}_q$ in $L'$ pointwise, that the action on units is induced by the action on $L'$, and that $\Phi$ is $D_w$-equivariant, and every finite extension $K_0$ of $\mathbb{Q}_q$ with [`ExtCitation.LocalLevel.IsBase q L' D_w K₀`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13) (i.e. $K_0 \leq L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_w$), every morphism $\theta$ of $D_w$-representations from $(L')^\times$ to $(F_{0,w})^\times$ whose underlying map is $\Phi^{-1}$, and every $u' \in H^2(D_w, (L')^\times)$ satisfying [`ExtCitation.LocalLevel.IsLocalFundamentalClass q L' D_w K₀ u'`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60), one has
--   $$\mathrm{inv}\,D_w\big((\mathrm{lam}_w)_*(\theta)_*u'\big) = \tfrac{1}{\#D_w} \bmod \mathbb{Z}.$$
--   A last unnamed hypothesis compares $\mathrm{invG}$ with $\mathrm{inv}\,\top$: for all $x$, $\mathrm{invG}(x) = \mathrm{inv}\,\top(\mathrm{res}_\top\,x)$.
--
--   **Local values at places above $S$.** Finally, $t : S \to \mathbb{N}$ and `ha` requires that for every finite place $w$ of $F_0$ and every $q \in S$ with $q \in w$,
--   $$\mathrm{inv}\,D_w\Big((\mathrm{lam}_w)_*\,(\rho_w)_*\,\mathrm{res}_{D_w}\,x\Big) = \frac{e \cdot f \cdot t_q}{p} \bmod \mathbb{Z},$$
--   where $e =$ `Ideal.ramificationIdx'` and $f =$ `Ideal.inertiaDeg'` of the ideal $(q)$ of $\mathbb{Z}$ relative to the contraction of $w$ along $\mathcal{O}_{E_0} \to \mathcal{O}_{F_0}$, and $\mathrm{res}_{D_w}$ is `groupCohomology.map` along $D_w \hookrightarrow G$ applied to the identity of the restricted module $F_0^\times$.
--
--   **Conclusion.** For every choice function $w$ assigning to each $q \in S$ and each finite place $v$ of $E_0$ a finite place $w(q,v)$ of $F_0$, if $w(q,v)$ lies over $v$ for all $q \in S$ and all $v \in V_q$, in the sense that the contraction of $w(q,v)$ along $\mathcal{O}_{E_0} \to \mathcal{O}_{F_0}$ equals $v$, then
--   $$\sum_{q \in S}\ \sum_{v \in V_q} \mathrm{inv}\,D_{w(q,v)}\Big((\mathrm{lam}_{w(q,v)})_*\,(\rho_{w(q,v)})_*\,\mathrm{res}_{D_{w(q,v)}}\,x\Big) = 0$$
--   in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the global reciprocity statement for the class $x$ in the form needed for the descent step: the local invariants of $x$, summed over one chosen place of $F_0$ above each place of $E_0$ lying above a prime of $S$, add up to zero, the contributions at all remaining places being zero because $F_0$ is unramified outside $S$ and $b$ takes values in $p$-th roots of unity. It is used in the assembly of the odd-$p$ layer statement [`groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two`](thm.html#groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two), where it supplies the vanishing clause accompanying the local computation of the invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2)

    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F₀] [IsGalois ℚ ↥F₀] [NumberField ↥F₀]
    (hF₀ : F₀.IsUnramifiedOutside S)
    (E₀ : IntermediateField ℚ ↥F₀) [NumberField ↥E₀]
    (hG : IsPGroup p (↥F₀ ≃ₐ[↥E₀] ↥F₀))

    (D : IdeleGaloisDescent (𝓞 ↥F₀) ↥E₀ ↥F₀)
    (_ : MulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀))
    (_ : ∀ (g : ↥F₀ ≃ₐ[↥E₀] ↥F₀) (c : IdeleClassGroup (𝓞 ↥F₀) ↥F₀), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 ↥F₀), (w.adicCompletion ↥F₀)ˣ →* (AdeleRing (𝓞 ↥F₀) ↥F₀)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (x : (w.adicCompletion ↥F₀)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 ↥F₀), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 ↥F₀),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (w.adicCompletion ↥F₀)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
          (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))
    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (x : (w.adicCompletion ↥F₀)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 ↥F₀) ↥F₀))
    (ρ : ∀ w : HeightOneSpectrum (𝓞 ↥F₀),
      Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (w.adicCompletion ↥F₀)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (u : (↥F₀)ˣ),
      (ρ w).hom (Additive.ofMul u) =
        Additive.ofMul (Units.map (algebraMap ↥F₀ (w.adicCompletion ↥F₀)).toMonoidHom u))
    (V : ↥S → Finset (HeightOneSpectrum (𝓞 ↥E₀)))
    (_ : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q ↔ (((q : Nat.Primes) : ℕ) : 𝓞 ↥E₀) ∈ v.asIdeal)

    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod p)
    (ζF : (↥F₀)ˣ) (hζp : ζF ^ p = 1)
    (b : (↥F₀ ≃ₐ[ℚ] ↥F₀) × (↥F₀ ≃ₐ[ℚ] ↥F₀) → Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ)
    (hb : ∀ (g h : ↥F₀ ≃ₐ[ℚ] ↥F₀) (ĝ ĥ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ y : ↥F₀, ĝ (y : AlgebraicClosure ℚ) = ((g y : ↥F₀) : AlgebraicClosure ℚ)) →
      (∀ y : ↥F₀, ĥ (y : AlgebraicClosure ℚ) = ((h y : ↥F₀) : AlgebraicClosure ℚ)) →
        b (g, h) = Additive.ofMul (ζF ^ ((f (ĝ, ĥ) : ZMod p).val)))
    (hbc : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ))
    (r : (↥F₀ ≃ₐ[↥E₀] ↥F₀) →* (↥F₀ ≃ₐ[ℚ] ↥F₀)) (hr : ∀ (g : ↥F₀ ≃ₐ[↥E₀] ↥F₀) (y : ↥F₀), r g y = g y)
    (φ : Rep.res r (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ) ⟶ Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ)
    (hφ : ∀ u : (↥F₀)ˣ, φ.hom (Additive.ofMul u) = Additive.ofMul u)
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))
    (hx : x = (groupCohomology.map r φ 2).hom ((H2π (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ)).hom ⟨b, hbc⟩))

    (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2) →+
      AddCircle (1 : ℚ))
    (inv : ∀ H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀),
      ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀))) 2) →+
        AddCircle (1 : ℚ))

    (_ : Function.Injective invG)
    (_ : ∀ H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀), Function.Injective (inv H))
    (_ : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (↥F₀ ≃ₐ[↥E₀] ↥F₀) • t = 0)
    (_ : ∀ (H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0)

    (_ : ∀ (H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀))
      (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2)),
      inv H ((groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))) 2).hom x) =
          H.index • invG x)

    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) L']
        [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (↥L')ˣ]
        (Φ : w.adicCompletion ↥F₀ ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (x : ℚ_[q]),
          g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (x : w.adicCompletion ↥F₀), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (w.adicCompletion ↥F₀)ˣ)
        (_ : ∀ v : (↥L')ˣ,
          ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion ↥F₀)ˣ) : w.adicCompletion ↥F₀) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) K₀ u'),
        inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) θ 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

    (_ : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2),
        invG x = inv ⊤ ((groupCohomology.map (⊤ : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)).subtype
          (𝟙 (Rep.res (⊤ : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)).subtype
            (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))) 2).hom x))

    (t : ↥S → ℕ)
    (ha : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (q : ↥S), (((q : Nat.Primes) : ℕ) : 𝓞 ↥F₀) ∈ w.asIdeal →
        inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (lam w) 2).hom
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (ρ w) 2).hom
              ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
                (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
                  (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x))) =
        ((((Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
              (Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) w.asIdeal) *
            Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
              (Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) w.asIdeal) * t q : ℕ) : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))) :
    ∀ w : ↥S → HeightOneSpectrum (𝓞 ↥E₀) → HeightOneSpectrum (𝓞 ↥F₀),
        (∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q →
          Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) (w q v).asIdeal = v.asIdeal) →
        ∑ q : ↥S, ∑ v ∈ V q,
          inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v))
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v))) (lam (w q v)) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v))) (ρ (w q v)) 2).hom
                ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v)).subtype
                  (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v)).subtype
                    (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x))) = 0 := by sorry
