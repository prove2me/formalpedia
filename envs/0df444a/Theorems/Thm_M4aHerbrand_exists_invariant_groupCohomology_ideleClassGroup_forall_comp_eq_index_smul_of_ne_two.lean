-- Prove2me | Theorems.Thm_M4aHerbrand_exists_invariant_groupCohomology_ideleClassGroup_forall_comp_eq_index_smul_of_ne_two
-- name    : M4aHerbrand.exists_invariant_groupCohomology_ideleClassGroup_forall_comp_eq_index_smul_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e5c9c799-57d0-5f8f-8fee-21930d06508f
-- title:
--   Invariant maps for the idèle class formation, p odd
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $F/E$ be a Galois extension of number fields with group $G = \mathrm{Gal}(F/E)$, and let $D$ be an idèle Galois descent datum for $F/E$, i.e. a homomorphism from $G$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$ which is continuous and compatible with $\mathrm{algebraMap}$ from $F$. Suppose $G$ acts multiplicatively and distributively on the idèle class group $C_F = (\mathbb{A}_F)^\times/\mathrm{principalIdeles}$ by the action induced by $D$ on classes. Suppose given, for every finite place $w$ of $F$, a homomorphism $\iota_w : F_w^\times \to (\mathbb{A}_F)^\times$ whose $w$-component is the identity and whose other finite components and infinite component are trivial, together with a morphism $\lambda_w$ of $\mathbb{Z}$-representations of the decomposition subgroup $D_w \leq G$ at $w$, from $F_w^\times$ to the restriction of $C_F$ along $D_w \hookrightarrow G$, given on elements by $x \mapsto$ the class of $\iota_w(x)$. Then there exist additive maps $\mathrm{inv}_G : H^2(G, C_F) \to \mathbb{Q}/\mathbb{Z}$ and, for every subgroup $H \leq G$, $\mathrm{inv}_H : H^2(H, C_F) \to \mathbb{Q}/\mathbb{Z}$ such that: all of them are injective; the image of $\mathrm{inv}_G$ is the $|G|$-torsion and that of $\mathrm{inv}_H$ the $|H|$-torsion of $\mathbb{Q}/\mathbb{Z}$; $\mathrm{inv}_H \circ \mathrm{res}^G_H = [G:H] \cdot \mathrm{inv}_G$, where restriction is the cohomology map along $H \hookrightarrow G$ with the identity on the restricted representation; and $\mathrm{inv}_G \circ \mathrm{cor} = \mathrm{inv}_H$ for every additive $\mathrm{cor} : H^2(H, C_F) \to H^2(G, C_F)$ satisfying $\mathrm{cor} \circ \mathrm{res}^G_H = [G:H] \cdot \mathrm{id}$. Moreover the local normalisation holds in its $p$-primary form at every finite place $w$: given a prime $q$, a finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying an action of $D_w$ that is trivial on $\mathbb{Q}_q$ and compatible with its action on $(L')^\times$, a $D_w$-equivariant ring isomorphism $\Phi : F_w \cong L'$, a finite extension $K_0$ of $\mathbb{Q}_q$ which is a base for $L'$ in the sense that $K_0 \leq L'$ and the elements of $L'$ lying in $K_0$ are exactly the $D_w$-invariants, a morphism $\theta$ of $D_w$-representations $(L')^\times \to F_w^\times$ inducing $\Phi^{-1}$ on elements, and a class $u' \in H^2(D_w, (L')^\times)$ satisfying the predicate [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) for $(q, L', D_w, K_0)$ (which pins $u'$ down, for every unramified overlay datum over $L'$, as the inflation of the cyclic carry cocycle built from a uniformiser), one has, for all naturals $m, a$ with $p$ coprime to $m$ and $m p^a = |D_w|$, $$m \cdot \mathrm{inv}_{D_w}\bigl(\lambda_{w*}\theta_*u'\bigr) = \frac{m}{|D_w|} \quad \text{in } \mathbb{Q}/\mathbb{Z},$$ the images of $u'$ being taken under the cohomology maps induced by $\theta$ and then $\lambda_w$ with the identity on $D_w$. The prime-to-$p$ part of the local invariant is thus left unconstrained.
--
--   This is the invariant-map package of Tate's class formation axioms for the idèle class group of a finite Galois extension of number fields: the Hasse principle and the computation of $H^2$ as a cyclic group of order $[F:E]$, the behaviour of $\mathrm{inv}$ under restriction and corestriction, and the normalisation of the invariant against the local fundamental classes, here in the form carrying only $p$-primary information at the finite places. It feeds the assembly of the Šafarevič–Tate pairing and the local-restriction statement for $H^1$ used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_invariant_groupCohomology_ideleClassGroup_forall_comp_eq_index_smul_of_ne_two.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_invariant_groupCohomology_ideleClassGroup_forall_comp_eq_index_smul_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
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
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)),
        m • inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F))
        (cor : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        (∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
          cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • x) →
        ∀ y : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2), invG (cor y) = inv H y) := by sorry
