-- Prove2me | Theorems.Thm_M4aHerbrand_finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
-- name    : M4aHerbrand.finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/263e22c6-d3ff-5a7e-85eb-2354e36d5fee
-- title:
--   Sum of local coordinates in ℚ/ℤ is unchanged by inflation
-- statement:
--   Three number fields $E$, $F$, $M$ are given, with $F$ an $E$-algebra, $M$ an $E$-algebra and an $F$-algebra forming a scalar tower over $E$, and with $F/E$ and $M/E$ Galois.
--
--   Descent and action data. `D` and `DM` are idèle Galois descent data for $F/E$ and $M/E$: each consists of a monoid homomorphism from the relevant Galois group to the ring automorphisms of the adèle ring ($\mathrm{Aut}(\mathbb{A}_F)$, resp. $\mathrm{Aut}(\mathbb{A}_M)$), compatible with the structure map from the field, and continuous for each group element. The Galois groups are equipped with multiplicative distributive actions on $(\mathbb{A}_F)^\times$ and $(\mathbb{A}_M)^\times$, and the hypotheses `hactI`, `hactIM` identify these actions with the ones induced on units by `D`, resp. `DM` (`unitsAct`).
--
--   Identification of the quotient. $S$ is a normal subgroup of $\operatorname{Gal}(M/E)$ and $\iota \colon \operatorname{Gal}(M/E)/S \xrightarrow{\ \sim\ } \operatorname{Gal}(F/E)$ is a group isomorphism; the hypothesis `hι` states that for every $g \in \operatorname{Gal}(M/E)$ and every $x \in F$ the image of $\iota(gS)(x)$ in $M$ equals $g$ applied to the image of $x$, i.e. $\iota$ is the canonical identification of $\operatorname{Gal}(M/E)/S$ with $\operatorname{Gal}(F/E)$ by restriction.
--
--   The global inflation morphism. $J$ is a morphism of $\mathbb{Z}$-linear representations of $\operatorname{Gal}(M/E)$ from the restriction along $\operatorname{Gal}(M/E) \to \operatorname{Gal}(M/E)/S \xrightarrow{\iota} \operatorname{Gal}(F/E)$ of the representation attached (additively) to $(\mathbb{A}_F)^\times$ to the representation attached to $(\mathbb{A}_M)^\times$; an unnamed hypothesis requires that $J$ be, on underlying elements, the map induced on units by the component $\beta$ of the adèle base change [`M4aHerbrand.GenuineDescent.genuineBaseChange F M`](def/M4aHerbrand_GenuineDescent.html#L87). Finally $y$ is an element of the degree-$2$ group cohomology of the representation of $\operatorname{Gal}(F/E)$ on $(\mathbb{A}_F)^\times$.
--
--   Local projections over $F$. `prG` assigns to each finite place $w$ of $F$ (a height-one prime of $\mathcal{O}_F$) a morphism of representations of the decomposition subgroup $\mathrm{decomp}\,(E,F,w) \le \operatorname{Gal}(F/E)$ — the decomposition subgroup of the valuation subring of $w$ — from the restriction of the global representation on $(\mathbb{A}_F)^\times$ to the representation on $(F_w)^\times$; an unnamed hypothesis requires each `prG w` to be given on underlying elements by the $w$-component homomorphism `finPart w` on idèle units.
--
--   Local models over $F$. For each finite place $v$ of $E$: a prime number $q(v)$; a finite extension $L'(v)$ of $\mathbb{Q}_{q(v)}$ inside a fixed algebraic closure, carrying a multiplicative–semiring action and a multiplicative distributive action on units of the decomposition subgroup $\mathrm{decomp}\,(E,F,\mathrm{above}(E,F,v))$ at the chosen place $\mathrm{above}(E,F,v)$ of $F$ over $v$; and a ring isomorphism $\Phi(v)$ from the completion $F_{\mathrm{above}(E,F,v)}$ onto $L'(v)$. Unnamed hypotheses require: the action fixes the image of $\mathbb{Q}_{q(v)}$ in $L'(v)$; the action on units is compatible with the coercion to $L'(v)$; and $\Phi(v)$ is equivariant. Further, $K_0(v)$ is a finite extension of $\mathbb{Q}_{q(v)}$ with [`ExtCitation.LocalLevel.IsBase`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13), i.e. $K_0(v) \le L'(v)$ and an element of $L'(v)$ lies in $K_0(v)$ exactly when it is fixed by the whole decomposition group. The morphism $\theta(v)$ of representations of that decomposition group goes from the representation on $(L'(v))^\times$ to the one on $(F_{\mathrm{above}(E,F,v)})^\times$, and an unnamed hypothesis requires it to be $\Phi(v)^{-1}$ on underlying elements. Finally $u'(v) \in H^2$ of the decomposition group acting on $(L'(v))^\times$ satisfies [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) for the data $(q(v), L'(v), \mathrm{decomp}, K_0(v))$: for every finite extension $M_0 \ge L'(v)$, every finite group $H$ acting faithfully on $M_0$ with normal subgroups $N_L$, $N_n$, an isomorphism $e$ of the decomposition group with $H/N_L$, an element $\varphi$ and a unit $\pi$ forming an unramified overlayer datum (base and layer fixed-field descriptions, compatibility of the two actions, $|H/N_n| = |\mathrm{decomp}|$, $\varphi$ generating $H/N_n$, a Frobenius congruence, and $\pi$ an $H$-invariant uniformiser of the base), and every equivariant lift of $L'(v)$-units to $M_0$-units over the coercion, the pullback of $u'(v)$ along $e^{-1} \circ \mathrm{mk}'$ equals the inflation from $H/N_n$ of the class of the carry $2$-cocycle built from $\varphi$ and $\pi$.
--
--   Local coordinates over $F$. $n \colon \{\text{finite places of }E\} \to \mathbb{Z}$, and an unnamed hypothesis requires, for every $v$, that the image of $y$ under the cohomology map in degree $2$ attached to the inclusion of $\mathrm{decomp}\,(E,F,\mathrm{above}(E,F,v))$ and to `prG (above E F v)` equals $n(v)$ times the image of $u'(v)$ under the degree-$2$ map attached to the identity of that group and to $\theta(v)$.
--
--   The $M$-side data. The same packages are given over $M$: `prM`, the local projections at the finite places of $M$ given by `finPart`; primes $q_M(v)$, finite extensions $L_M(v)$ with actions of $\mathrm{decomp}\,(E,M,\mathrm{above}(E,M,v))$, isomorphisms $\Phi_M(v)$ onto the completions $M_{\mathrm{above}(E,M,v)}$ with the three compatibility hypotheses, base fields $K_M(v)$ satisfying `IsBase`, morphisms $\theta_M(v)$ realising $\Phi_M(v)^{-1}$, and classes $u_M(v)$ satisfying `IsLocalFundamentalClass` for the $M$-side data — all with the same content as above, and summarised here. The integers $n_M(v)$ are the local coordinates of the inflated class: an unnamed hypothesis requires, for every $v$, that the image under the degree-$2$ map attached to the inclusion of $\mathrm{decomp}\,(E,M,\mathrm{above}(E,M,v))$ and to `prM (above E M v)` of the inflation of $y$ along $(\iota \circ \mathrm{mk}'_S, J)$ equals $n_M(v)$ times the image of $u_M(v)$ under the degree-$2$ map attached to the identity and to $\theta_M(v)$.
--
--   Conclusion. In $\mathbb{Q}/\mathbb{Z}$, realised as `AddCircle (1 : ℚ)`, the two sums over all finite places $v$ of $E$, taken in the sense of `∑ᶠ`, agree:
--   $$\sum_{v}^{\ \mathrm{f}} \ \frac{n_M(v)}{\bigl|\mathrm{decomp}\,(E,M,\mathrm{above}(E,M,v))\bigr|} \ = \ \sum_{v}^{\ \mathrm{f}} \ \frac{n(v)}{\bigl|\mathrm{decomp}\,(E,F,\mathrm{above}(E,F,v))\bigr|},$$
--   the cardinalities being `Nat.card` of the respective decomposition subgroups and each rational being taken modulo $1$.
--
--   This is the statement that the sum of the local invariants of a degree-$2$ idèle class is unchanged when the class is inflated up a tower $E \subseteq F \subseteq M$ of Galois layers, the local invariant at a place $W$ of $M$ being computed against the local fundamental class of the decomposition group at $W$. It is used to transport the local–global identity for the sum of invariants along an auxiliary layer, and is cited by [`M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup`](thm.html#M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup) and [`M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isPGroup`](thm.html#M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))

    (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))
    (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

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
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom y =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v))

    (prM : ∀ w : HeightOneSpectrum (𝓞 M),
      Rep.res (NumberField.PlaceDecomp.decomp E M w).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M w)) (w.adicCompletion M)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 M)) (x : (AdeleRing (𝓞 M) M)ˣ), (prM w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (qM : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (qM v).Prime)
    (LM : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[qM v] (PadicAlgCl (qM v)))
    (_ : ∀ v, FiniteDimensional ℚ_[qM v] (LM v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (LM v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ)
    (ΦM : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E M v).adicCompletion M ≃+* LM v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : ℚ_[qM v]), g • algebraMap ℚ_[qM v] (LM v) y = algebraMap ℚ_[qM v] (LM v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : (↥(LM v))ˣ), ((g • y : (↥(LM v))ˣ) : LM v) = g • (y : LM v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : (NumberField.PlaceAbove.above E M v).adicCompletion M), (ΦM v) (g • y) = g • (ΦM v) y)
    (KM : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[qM v] (PadicAlgCl (qM v)))
    (_ : ∀ v, FiniteDimensional ℚ_[qM v] (KM v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (qM v) (LM v) (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (KM v))
    (θM : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) ((NumberField.PlaceAbove.above E M v).adicCompletion M)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(LM v))ˣ),
      ((Additive.toMul ((θM v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E M v).adicCompletion M)ˣ) : (NumberField.PlaceAbove.above E M v).adicCompletion M) =
        (ΦM v).symm (y : LM v))
    (uM : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (qM v) (LM v) (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (KM v) (uM v))

    (nM : HeightOneSpectrum (𝓞 E) → ℤ)
    (_ : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)).subtype (prM (NumberField.PlaceAbove.above E M v)) 2).hom ((groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) J 2).hom y) =
        nM v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (θM v) 2).hom (uM v)) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((nM v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by sorry
