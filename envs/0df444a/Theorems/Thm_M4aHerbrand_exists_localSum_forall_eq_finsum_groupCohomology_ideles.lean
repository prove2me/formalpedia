-- Prove2me | Theorems.Thm_M4aHerbrand_exists_localSum_forall_eq_finsum_groupCohomology_ideles
-- name    : M4aHerbrand.exists_localSum_forall_eq_finsum_groupCohomology_ideles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/792b23c4-fa1a-53f7-baaa-ba86e2de3551
-- title:
--   A local-sum invariant on H²(G,I_F) for cyclic extensions
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois and $G = \mathrm{Gal}(F/E)$ cyclic, let $D$ be an idèle Galois descent datum for $F/E$ (a monoid homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, compatible with the structure map $F \to \mathbb{A}_F$ and continuous in each $g$), and equip $\mathbb{A}_F^{\times}$ with a multiplicative $G$-action assumed to agree with the one induced by $D$ on units. Then there is an additive homomorphism $\Lambda$ from $H^{2}(G, \mathbb{A}_F^{\times})$ to $\mathrm{AddCircle}\,(1:\mathbb{Q}) = \mathbb{Q}/\mathbb{Z}$ with the following property, for every choice of the data: a family `prG` of morphisms of representations from the restriction of $\mathbb{A}_F^{\times}$ to the decomposition subgroup $D_w \le G$ at each finite place $w$ of $F$ into $(F_w^{\times})$, pinned by the requirement that it be the $w$-component map `finPart w`; a class $x \in H^{2}(G,\mathbb{A}_F^{\times})$; for each finite place $v$ of $E$ a prime $q_v$, a finite extension $L'_v$ of $\mathbb{Q}_{q_v}$ inside a fixed algebraic closure carrying a semiring action of $D_{w(v)}$, where $w(v)$ is the chosen place `above` $v$, together with a $D_{w(v)}$-equivariant ring isomorphism $\Phi_v \colon F_{w(v)} \xrightarrow{\sim} L'_v$, the actions being trivial on $\mathbb{Q}_{q_v}$ and compatible with the action on units; a finite extension $K_{0,v}$ of $\mathbb{Q}_{q_v}$ which is a base for $L'_v$ in the sense of [`ExtCitation.LocalLevel.IsBase`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13) ($K_{0,v} \le L'_v$ and the elements of $L'_v$ in $K_{0,v}$ are exactly those fixed by all of $D_{w(v)}$); a morphism of representations $\theta_v$ from $(L'_v)^{\times}$ to $F_{w(v)}^{\times}$ realising $\Phi_v^{-1}$ on underlying elements; a class $u'_v \in H^{2}(D_{w(v)}, (L'_v)^{\times})$ which is a local fundamental class in the sense of [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) (its image under any value-pinned transfer to an unramified overlay datum is the inflation of the class of the cyclic carry cocycle of the prescribed uniformiser); and integers $n_v$ such that, for every $v$, the image of $x$ under the degree-$2$ map induced by the inclusion $D_{w(v)} \hookrightarrow G$ and by `prG` at $w(v)$ equals $n_v$ times the image of $u'_v$ under $\theta_v$ in degree $2$. Under these hypotheses $\Lambda x = \sum^{f}_{v} n_v / \#D_{w(v)}$ in $\mathbb{Q}/\mathbb{Z}$, the sum being over the finite places of $E$.
--
--   This is the invariant map on the idèle cohomology of a cyclic layer, classically $x \mapsto \sum_v \mathrm{inv}_v(x_v)$, here packaged as a single additive map to $\mathbb{Q}/\mathbb{Z}$ whose values are prescribed by any reading of the local coordinates of a class against local fundamental classes, with no local invariant isomorphisms mentioned. It feeds the construction of the surjective invariant map used in the cyclic-layer step of the computation of the idèle class cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_localSum_forall_eq_finsum_groupCohomology_ideles.lean

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
open CategoryTheory NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_localSum_forall_eq_finsum_groupCohomology_ideles
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    :
    ∃ Λ : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2) →+ AddCircle (1 : ℚ),
      (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
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
        Λ x =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by sorry
