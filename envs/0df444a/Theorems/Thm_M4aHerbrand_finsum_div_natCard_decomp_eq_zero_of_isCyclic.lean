-- Prove2me | Theorems.Thm_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isCyclic
-- name    : M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/1acd4b08-20af-569f-86b4-55622e9275e6
-- title:
--   Local readings of a global class sum to zero: cyclic layer
-- statement:
--   Let $F/E$ be an extension of number fields which is Galois with cyclic group $G = \mathrm{Gal}(F/E)$, and let $D$ be a descent datum for the idèles of $F$: a homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_F$ (the adele ring of $\mathcal{O}_F$ in $F$) which is continuous in each component and compatible with the structure map $F \to \mathbb{A}_F$. Fix actions of $G$ on $\mathbb{A}_F^\times$ (required to be the one induced by $D$) and on $F^\times$ (required to be the Galois action), and let $j$ be the morphism of $\mathbb{Z}[G]$-representations $F^\times \to \mathbb{A}_F^\times$ induced by the principal idèle map. Assume that every element of $G$ fixing an infinite place of $F$ is trivial. Let $\alpha \in H^2(G, F^\times)$. For every finite place $w$ of $F$ let $\mathrm{pr}_{G,w}$ be a morphism, over the decomposition subgroup $D_w \le G$ of the valuation subring of $w$, from the restriction of $\mathbb{A}_F^\times$ to $(F_w)^\times$, required to be the $w$-component map `finPart`. For each finite place $v$ of $E$ let $q_v$ be a prime, let $L'_v$ be a finite extension of $\mathbb{Q}_{q_v}$ inside a fixed algebraic closure, carrying an action of the decomposition group $D_{w(v)}$ of the chosen place $w(v)$ of $F$ above $v$ that fixes $\mathbb{Q}_{q_v}$ pointwise and is compatible with the action on units, and let $\Phi_v$ be a $D_{w(v)}$-equivariant ring isomorphism $F_{w(v)} \cong L'_v$; let $K_{0,v}$ be a finite extension of $\mathbb{Q}_{q_v}$ which is the base of $L'_v$ for $D_{w(v)}$ in the sense that $K_{0,v} \le L'_v$ and an element of $L'_v$ lies in $K_{0,v}$ exactly when it is fixed by all of $D_{w(v)}$; let $\theta_v$ be the morphism of representations $(L'_v)^\times \to (F_{w(v)})^\times$ induced by $\Phi_v^{-1}$, and let $u'_v \in H^2(D_{w(v)}, (L'_v)^\times)$ satisfy the predicate `IsLocalFundamentalClass` for $(q_v, L'_v, D_{w(v)}, K_{0,v})$, which pins $u'_v$ down by demanding that in every unramified overlayer datum above $L'_v$ its image is the inflation of the carry class of the chosen uniformiser. Finally let $n : v \mapsto n_v$ be integers such that for every finite place $v$ of $E$ the local coordinate at $w(v)$ of $H^2(j)(\alpha)$, that is the image of $\alpha$ under $H^2(j)$ followed by restriction to $D_{w(v)}$ along $\mathrm{pr}_{G,w(v)}$, equals $n_v$ times the image of $u'_v$ under $H^2(\theta_v)$. The conclusion is that the finitely supported sum over all finite places $v$ of $E$ of the classes of $n_v / \lvert D_{w(v)} \rvert$ in $\mathbb{Q}/\mathbb{Z}$, realised as `AddCircle (1 : ℚ)`, vanishes.
--
--   This is Tate's reciprocity law $\sum_v \mathrm{inv}_v(\alpha) = 0$ for a class $\alpha$ in $H^2(\mathrm{Gal}(F/E), F^\times)$ in the case of a cyclic layer, stated without any invariant map: only the integer readings $n_v$ of the local coordinates against the local fundamental classes occur. It feeds the corresponding statement for $p$-group layers and the assembly of the global invariant used in the idèle class formation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isCyclic.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
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

theorem M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isCyclic
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (j : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hj : ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (α : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

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
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom α) =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) = 0 := by sorry
