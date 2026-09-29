-- Prove2me | Theorems.Thm_M4aHerbrand_map_prG_eq_smul_sylow_of_map_prG_eq_smul
-- name    : M4aHerbrand.map_prG_eq_smul_sylow_of_map_prG_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/aa19de93-40e2-5b3a-a3d4-c15946f8b6a3
-- title:
--   Restriction to the Sylow fixed field preserves the local coordinates
-- statement:
--   Throughout, $E$ and $F$ are number fields with $F/E$ Galois, $p$ is a prime and $P$ is a Sylow $p$-subgroup of $G = \mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$; write $E' =$ `IntermediateField.fixedField` $(P)$ for the fixed field of (the underlying subgroup of) $P$ inside $F$, so that $G' = \mathrm{Gal}(F/E')$, and $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`.
--
--   **Galois action on the ideles (two copies).** The datum $D$ is an `IdeleGaloisDescent (𝓞 F) E F`, i.e. a monoid homomorphism `act` from $G$ to the ring automorphisms of $\mathbb{A}_F$ such that `act g` commutes with the structure map $F \to \mathbb{A}_F$ and $g$ on $F$, and such that each `act g` is continuous. Alongside a `MulDistribMulAction` of $G$ on $\mathbb{A}_F^{\times}$, the hypothesis `hactI` states that this action is the one induced by $D$: $g \bullet x = D.\mathrm{unitsAct}\, g\, x$ for all $g$ and all $x \in \mathbb{A}_F^{\times}$, where `unitsAct` is the functorial action of `act g` on units. The family `prG` assigns to every finite place $w$ of $F$ (a height-one prime of $\mathcal{O}_F$) a morphism of $\mathbb{Z}$-representations of the decomposition subgroup $G_w =$ [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) (the decomposition subgroup in $G$ of the valuation subring of the $w$-adic valuation) from the restriction of $\mathbb{A}_F^{\times}$ to $G_w$ into $(F_w)^{\times}$, the units of the $w$-adic completion; `hprG` identifies it on elements with the $w$-component homomorphism `finPart w` (evaluation at $w$ of the finite part of an idelic unit). The quadruple $D'$, `hactI'`, `prG'`, `hprG'` is the same package for the base field $E'$ in place of $E$: a descent datum $D'$ for $\mathrm{Gal}(F/E')$, a `MulDistribMulAction` of $G'$ on $\mathbb{A}_F^{\times}$ agreeing with $D'.\mathrm{unitsAct}$, and a family of $w$-component morphisms for the decomposition subgroups taken inside $G'$.
--
--   **Comparison of the two Galois groups.** The map $\Theta$ is a multiplicative equivalence from $P$ (as a subgroup of $G$) onto $G'$, with `hΘ` asserting that $\Theta s$ acts on $F$ as $s$ does; $\psi$ is a morphism of representations of $P$ from the restriction of $\mathbb{A}_F^{\times}$ along $\Theta$ to the restriction of $\mathbb{A}_F^{\times}$ along the inclusion $P \hookrightarrow G$, and `hψ` says that $\psi$ is the identity on underlying elements.
--
--   **The two cohomology classes.** $x$ lies in $H^2(G, \mathbb{A}_F^{\times})$ and $x'$ in $H^2(G', \mathbb{A}_F^{\times})$ (both in the form `groupCohomology … 2`), and `hx'` requires that the image of $x'$ under the map induced by $(\Theta, \psi)$ coincides with the image of $x$ under the map induced by the inclusion $P \hookrightarrow G$ with identity coefficient morphism; that is, $x'$ restricts, via $\Theta$, to the restriction of $x$ to $P$.
--
--   **Local data at the finite places of $E$.** For every height-one prime $v$ of $\mathcal{O}_E$ there are: a prime $q(v)$; an intermediate field $L_v$ of $\mathbb{Q}_{q(v)} \subseteq$ `PadicAlgCl (q v)`, finite over $\mathbb{Q}_{q(v)}$; actions of the decomposition subgroup $G_{w(v)}$ at the chosen place $w(v) =$ [`NumberField.PlaceAbove.above E F v`](def/NumberField_PlaceAbove.html#L27) above $v$ on $L_v$ by semiring automorphisms and on $L_v^{\times}$ multiplicatively; and a ring isomorphism $\Phi_v$ from the $w(v)$-adic completion of $F$ onto $L_v$. Three unnamed compatibility hypotheses require that $G_{w(v)}$ fixes the image of $\mathbb{Q}_{q(v)}$ in $L_v$ pointwise, that the action on $L_v^{\times}$ is compatible with the coercion into $L_v$, and that $\Phi_v$ is $G_{w(v)}$-equivariant. A further intermediate field $K_{0,v}$, finite over $\mathbb{Q}_{q(v)}$, satisfies [`ExtCitation.LocalLevel.IsBase`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13), i.e. $K_{0,v} \le L_v$ and an element of $L_v$ lies in $K_{0,v}$ exactly when it is fixed by every element of $G_{w(v)}$ (so $K_{0,v}$ is the fixed field). The morphism $\theta_v$ of representations of $G_{w(v)}$ goes from $L_v^{\times}$ to $(F_{w(v)})^{\times}$ and is required to be given on elements by $\Phi_v^{-1}$. Finally $u_v \in H^2(G_{w(v)}, L_v^{\times})$ satisfies [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60): for every finite overlayer $M \ge L_v$ inside the algebraic closure, every finite group $H$ acting faithfully on $M$ with compatible action on $M^{\times}$, normal subgroups $N_L, N_n \le H$, an isomorphism $e : G_{w(v)} \simeq H/N_L$, an element $\varphi \in H$ and a unit $\pi$ of $M$ forming an `IsUnramOverlayerDatum` (twelve clauses, summarised here: the $\mathbb{Q}_{q}$-scalars are fixed and the action on units is compatible with coercion; $K_{0,v}$ and $L_v$ are cut out inside $M$ as the fixed fields of $H$ and of $N_L$; $e$ matches the two actions; $\#(H/N_n) = \#G_{w(v)}$ and $H/N_n$ is generated by the image of $\varphi$; $\varphi$ acts as the Frobenius on the $N_n$-fixed elements of absolute value $\le 1$; and $\pi$ is an $H$-fixed uniformiser lying in $K_{0,v}$, of maximal absolute value among the $N_n$-fixed elements of absolute value $<1$), and every comparison morphism $\iota$ along $e^{-1}$ composed with $H \to H/N_L$ which induces the inclusion $L_v \subseteq M$ on elements, the image of $u_v$ under the induced map on $H^2$ is the inflation from $H/N_n$ of the class of the explicit cyclic "carry" $2$-cocycle `carryFun` attached to the image of $\varphi$ and to $\pi$.
--
--   **The coordinates of $x$.** An integer-valued function $n$ on the height-one primes of $\mathcal{O}_E$ is given, with `hn`: for every $v$, the image of $x$ under the map induced by the inclusion $G_{w(v)} \hookrightarrow G$ and the coefficient morphism `prG (above E F v)` equals $n(v)$ times the image of $u_v$ under the map induced by the identity of $G_{w(v)}$ and $\theta_v$.
--
--   **Local data at the finite places of $E'$.** For every height-one prime $v'$ of $\mathcal{O}_{E'}$ the same package is given with primes $q'(v')$, fields $L'_{v'}$ finite over $\mathbb{Q}_{q'(v')}$, actions of the decomposition subgroup (taken inside $G'$) at the chosen place above $v'$ on $L'_{v'}$ and on $L'^{\times}_{v'}$, an equivariant ring isomorphism $\Phi'_{v'}$ from the corresponding completion of $F$ onto $L'_{v'}$ together with the three compatibility hypotheses, fixed fields $K'_{0,v'}$ finite over $\mathbb{Q}_{q'(v')}$ satisfying `IsBase`, morphisms $\theta'_{v'}$ given on elements by $\Phi'^{-1}_{v'}$, and classes $u'_{v'} \in H^2$ of the decomposition subgroup with coefficients in $L'^{\times}_{v'}$ satisfying `IsLocalFundamentalClass` with base $K'_{0,v'}$. No analogue of `n` or `hn` is assumed on this side.
--
--   **Conclusion.** For every height-one prime $v'$ of $\mathcal{O}_{E'}$, the image of $x'$ under the map on $H^2$ induced by the inclusion of the decomposition subgroup at the chosen place above $v'$ into $G'$ together with the coefficient morphism `prG'` at that place equals
--   $$n\bigl(v' \cap \mathcal{O}_E\bigr) \cdot \bigl(\text{image of } u'_{v'} \text{ under the map induced by the identity and } \theta'_{v'}\bigr),$$
--   where $v' \cap \mathcal{O}_E$ is `v'.under (𝓞 E)`, the prime of $\mathcal{O}_E$ lying under $v'$. In other words, the local coordinate of $x'$ at the chosen place above $v'$, read against the local fundamental class of the layer at that place, is the integer attached to the place of $E$ beneath $v'$.
--
--   The proof cites [`M4aHerbrand.map_prG_eq_smul_fixedField_of_map_prG_eq_smul`](thm.html#M4aHerbrand.map_prG_eq_smul_fixedField_of_map_prG_eq_smul), the corresponding assertion for the fixed field of an arbitrary subgroup $H \le G$, with $H$ the underlying subgroup of $P$; only that subgroup, and not the Sylow property, enters the conclusion.
--
--   A bookkeeping step in the Sylow descent of Tate's canonical-class computation, transporting the place-by-place description of a global degree-two idele-class cohomology class from the ground field $E$ to the fixed field of a Sylow $p$-subgroup, where the degree formula identifies the coordinate index with the place lying underneath. It is used by [`M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero), which passes from $p$-group layers to an arbitrary finite Galois layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_prG_eq_smul_sylow_of_map_prG_eq_smul.lean

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

theorem M4aHerbrand.map_prG_eq_smul_sylow_of_map_prG_eq_smul
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (D' : IdeleGaloisDescent (𝓞 F) ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F)
    [MulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI' : ∀ (g : (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D'.unitsAct g x)
    (prG' : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F w)) (w.adicCompletion F)ˣ)
    (hprG' : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG' w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (Θ : ↥(P : Subgroup (F ≃ₐ[E] F)) ≃* (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F))
    (hΘ : ∀ (s : ↥(P : Subgroup (F ≃ₐ[E] F))) (y : F), Θ s y = (s : F ≃ₐ[E] F) y)
    (ψ : Rep.res Θ.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res (P : Subgroup (F ≃ₐ[E] F)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
    (hψ : ∀ y, ψ.hom y = y)
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (x' : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (hx' : (groupCohomology.map Θ.toMonoidHom ψ 2).hom x' =
      (groupCohomology.map (P : Subgroup (F ≃ₐ[E] F)).subtype (𝟙 (Rep.res (P : Subgroup (F ≃ₐ[E] F)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) 2).hom x)

    (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
    (L : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L v) y = algebraMap ℚ_[q v] (L v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L v))ˣ), ((g • y : (↥(L v))ˣ) : L v) = g • (y : L v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
    (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
    (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L v))ˣ),
      ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L v))
    (u : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u v))
    (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (hn : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u v))

    (q' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))) → ℕ) (_ : ∀ v, Fact (q' v).Prime)
    (L' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q' v] (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (↥(L' v))ˣ)
    (Φ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F ≃+* L' v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (y : ℚ_[q' v]), g • algebraMap ℚ_[q' v] (L' v) y = algebraMap ℚ_[q' v] (L' v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F), (Φ' v) (g • y) = g • (Φ' v) y)
    (K₀' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q' v] (K₀' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), ExtCitation.LocalLevel.IsBase (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (K₀' v))
    (θ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (↥(L' v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (y : (↥(L' v))ˣ),
      ((Additive.toMul ((θ' v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F) =
        (Φ' v).symm (y : L' v))
    (u' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (↥(L' v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), ExtCitation.LocalLevel.IsLocalFundamentalClass (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (K₀' v) (u' v)) :
    ∀ v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v')).subtype (prG' (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v')) 2).hom x' =
        n (v'.under (𝓞 E)) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v'))) (θ' v') 2).hom (u' v') := by sorry
