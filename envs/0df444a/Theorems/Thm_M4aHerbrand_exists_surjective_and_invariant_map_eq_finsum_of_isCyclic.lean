-- Prove2me | Theorems.Thm_M4aHerbrand_exists_surjective_and_invariant_map_eq_finsum_of_isCyclic
-- name    : M4aHerbrand.exists_surjective_and_invariant_map_eq_finsum_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/2eac1e95-478d-5c6a-a904-14e86451beda
-- title:
--   Invariant map on H²(G,C_F) for cyclic layers
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois and $G = \mathrm{Gal}(F/E)$ cyclic, and let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_F$, $E$, $F$: a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$, each automorphism continuous and compatible with the structure map $F \to \mathbb{A}_F$ via the action on $F$. Assume $G$ acts multiplicatively and distributively on $\mathbb{A}_F^\times$ and on the idèle class group $C_F = \mathbb{A}_F^\times / F^\times$ by the actions induced by $D$ (hypotheses `hactI`, `hact`), and that every infinite place $v$ of $F$ has trivial stabiliser in $G$. Then two things hold. First, for every morphism $\pi$ of $\mathbb{Z}[G]$-representations $\mathbb{A}_F^\times \to C_F$ whose underlying map is the quotient map, the induced map $H^2(G,\mathbb{A}_F^\times) \to H^2(G,C_F)$ is surjective. Secondly, there is an additive homomorphism $\mathrm{inv}_G : H^2(G,C_F) \to \mathbb{Q}/\mathbb{Z}$ which is injective, whose range is exactly the $|G|$-torsion $\{t : |G| \cdot t = 0\}$, and which computes global invariants as sums of local ones: given componentwise projections $\mathrm{prG}_w$ onto $(F_w)^\times$ (realised by `finPart`) restricted to the decomposition subgroup $D_w$ at each finite place $w$ of $F$, given $\pi$ as above and $x \in H^2(G,\mathbb{A}_F^\times)$, and given for each finite place $v$ of $E$ a prime $q(v)$, a finite extension $L'_v/\mathbb{Q}_{q(v)}$ inside a fixed algebraic closure with $D_{w(v)}$-action ($w(v)$ the chosen place of $F$ above $v$), a $D_{w(v)}$-equivariant ring isomorphism $\Phi_v : F_{w(v)} \to L'_v$ with compatible unit morphism $\theta_v$ inverse to it, a finite base field $K_{0,v}$ which is precisely the $D_{w(v)}$-fixed subfield of $L'_v$, and a class $u'_v \in H^2(D_{w(v)}, (L'_v)^\times)$ that is a local fundamental class in the sense of [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) (its comparison image along any unramified overlay of $L'_v$ with Frobenius lift $\varphi$ and $H$-invariant uniformiser $\pi$ equals the inflation of the class of the associated 'carry' $2$-cocycle), together with integers $n_v$ such that the local component of $x$ in $H^2(D_{w(v)}, F_{w(v)}^\times)$ equals $n_v$ times the image of $u'_v$ under $\theta_v$, one has $$\mathrm{inv}_G\big(H^2(\pi)(x)\big) = \sum_{v}\ \frac{n_v}{|D_{w(v)}|} \bmod 1,$$ the sum being the finitely supported sum over the finite places $v$ of $E$, and $\mathbb{Q}/\mathbb{Z}$ being realised as `AddCircle (1 : ℚ)`.
--
--   This is the cyclic case of Tate's description of the invariant map of the idèle class formation: $H^2(G, C_F)$ is cyclic of order $|G|$, identified with $\tfrac{1}{|G|}\mathbb{Z}/\mathbb{Z}$, and the invariant of a class lifted from the idèles is the sum of the local invariants of its components. It is the base case for the passage to $p$-groups in [`M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup`](thm.html#M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup), on the way to the class formation axioms underlying global class field theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_surjective_and_invariant_map_eq_finsum_of_isCyclic.lean

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

theorem M4aHerbrand.exists_surjective_and_invariant_map_eq_finsum_of_isCyclic
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1) :

    (∀ (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
      (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)),
      ∀ c : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
        ∃ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2),
          (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x = c) ∧
    ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ)),

      Function.Injective invG ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧

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
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by sorry
