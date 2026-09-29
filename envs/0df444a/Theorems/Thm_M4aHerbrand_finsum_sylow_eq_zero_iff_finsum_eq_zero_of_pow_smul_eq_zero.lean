-- Prove2me | Theorems.Thm_M4aHerbrand_finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero
-- name    : M4aHerbrand.finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/700f718a-0d44-5767-9eec-687c65d904a1
-- title:
--   Sylow descent for vanishing of a sum of local invariants
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $p$ be a prime and let $P$ be a Sylow $p$-subgroup of $\mathrm{Gal}(F/E)$. Let $D$ be an `IdeleGaloisDescent`, i.e. a homomorphism from $\mathrm{Gal}(F/E)$ to the ring automorphisms of $\mathrm{AdeleRing}\,(\mathcal{O}_F, F)$ which is continuous in each $g$ and compatible with the action on $F$, and suppose the ambient multiplicative-distributive action of $\mathrm{Gal}(F/E)$ on the idèle units is the one induced by $D$. For each finite place $w$ of $F$ let `prG w` be a morphism of representations from the restriction of the idèle units to the decomposition subgroup $D_w$ (the stabiliser of the valuation subring of $w$) into the units of the $w$-adic completion, realising the coordinate map `finPart w`. Let $x \in H^2(\mathrm{Gal}(F/E), \mathbb{I}_F^\times)$. For each finite place $v$ of $E$ there are given: a prime $q_v$; a finite extension $L_v$ of $\mathbb{Q}_{q_v}$ inside a fixed algebraic closure, carrying an action of the decomposition subgroup at the chosen place $w(v)$ above $v$ which fixes $\mathbb{Q}_{q_v}$, is compatible with the unit action, and is transported from the completion $F_{w(v)}$ by an equivariant ring isomorphism $\Phi_v$; a finite extension $K_{0,v}$ of $\mathbb{Q}_{q_v}$ which is the base of $L_v$ in the sense of [`ExtCitation.LocalLevel.IsBase`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13), namely $K_{0,v} \le L_v$ and an element of $L_v$ lies in $K_{0,v}$ exactly when it is fixed by the whole decomposition subgroup; a morphism $\theta_v$ of representations of units induced by $\Phi_v^{-1}$; and a class $u_v \in H^2(D_{w(v)}, L_v^\times)$ satisfying [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60). Let $n : v \mapsto n_v \in \mathbb{Z}$ be such that the localisation of $x$ at $w(v)$, i.e. its image under the map induced by the inclusion $D_{w(v)} \hookrightarrow \mathrm{Gal}(F/E)$ and `prG`, equals $n_v$ times the image of $u_v$ under $\theta_v$, and let $k$ satisfy $p^k \cdot x = 0$. The conclusion is that, writing $E'$ for the fixed field of $P$, the finite sum over the finite places $v'$ of $E'$ of $n_{v'|E}/\#D'_{w'(v')}$ in $\mathbb{Q}/\mathbb{Z} = \mathrm{AddCircle}\,1$ vanishes if and only if the corresponding sum over the finite places $v$ of $E$ of $n_v/\#D_{w(v)}$ vanishes, the decomposition subgroups being taken over $E'$ and over $E$ respectively.
--
--   This is the Sylow-descent bookkeeping step in Tate's computation of the invariant of a global degree-two class: it transfers the vanishing of the sum of local invariants between the base field and the fixed field of a Sylow $p$-subgroup, for a class killed by a power of $p$. It is used in the passage from layers with $p$-group Galois group to an arbitrary finite Galois layer, and is cited by [`M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero.lean

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

theorem M4aHerbrand.finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
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
    (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0) :
    (∑ᶠ v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))),
        ((((n (v'.under (𝓞 E)) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v')) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) = 0 ↔
      (∑ᶠ v : HeightOneSpectrum (𝓞 E),
        ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) = 0 := by sorry
