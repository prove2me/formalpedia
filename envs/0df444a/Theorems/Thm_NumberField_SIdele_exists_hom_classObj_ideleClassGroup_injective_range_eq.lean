-- Prove2me | Theorems.Thm_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq
-- name    : NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/06cd6b19-e63b-5d42-8a5d-3461b0f4521a
-- title:
--   S-idèle class module embeds into the idèle class group
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, write $G = K \simeq_{\mathrm{alg}[E]} K$ for the Galois group, let $S$ be a finite set of height-one primes of $\mathcal{O}_E$, and let $D$ be an idèle Galois descent datum for $\mathcal{O}_K$, $E$, $K$, that is, a monoid homomorphism $g \mapsto D.\mathrm{act}(g)$ from $G$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal{O}_K, K)$, each continuous, compatible with the structure map $K \to \mathrm{AdeleRing}(\mathcal{O}_K,K)$ and the action of $g$ on $K$. Assume a multiplicative distributive action of $G$ on the idèle class group $(\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times / \mathrm{principalIdeles}$ which agrees with the action `D.classAct` induced by $D$. Then there exist an additive homomorphism $\Phi$ from the underlying group of the $S$-idèle representation [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) (the product of the coinduced local fibres at the places of $E$ in $S$, outside $S$, and at infinity) to $\mathrm{Additive}\,(\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$, and a morphism $\iota$ in $\mathrm{Rep}\,\mathbb{Z}\,G$ from the $S$-idèle class module [`NumberField.SIdele.classObj E K S`](def/NumberField_SIdeleModule.html#L104) (the quotient of `obj E K S` by the range of the diagonal $S$-unit map `diag E K S`) to the idèle class group with its $G$-action, such that: $\Phi$ is injective; the range of $\Phi$ is the subgroup `unitIdelesOutside` of adelic units integral, together with their inverses, at every prime $w$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_E$ lies outside $S$; $\Phi(\rho(g)x) = D.\mathrm{unitsAct}(g)(\Phi x)$ for all $g \in G$; $\Phi$ composed with `diag E K S` is the principal-idèle embedding of $S$-units; $\iota$ of the class of $y$ is the class of $\Phi y$ modulo principal idèles; $\iota$ is injective; and the range of $\iota$ is the image of `unitIdelesOutside` under the projection to the idèle class group.
--
--   This is the comparison between the explicit product model of the $S$-idèle class module $C_{K,S} = J_{K,S}/\mathcal{O}_{K,S}^\times$, in which Shapiro's lemma applies fibre by fibre, and the idèle class group $C_K$ carrying the global class formation: the embedding $C_{K,S} \hookrightarrow C_K$ with image $\mathbb{I}_K^{S_K}K^\times/K^\times$, as in the standard treatment of the $S$-idèle class sequence. It is used by the level-arithmetic lemmas on $S$-idèle coboundaries.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

theorem NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K)]
    (hact : ∀ (g : K ≃ₐ[E] K) (c : M4aHerbrand.IdeleClassGroup (𝓞 K) K), g • c = D.classAct g c) :
    ∃ (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
      (ι : NumberField.SIdele.classObj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K)),
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
        Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x)))) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) ∧
      (∀ y : NumberField.SIdele.obj E K S, ι.hom ((NumberField.SIdele.toClass E K S).hom y) =
        Additive.ofMul (QuotientGroup.mk (Additive.toMul (Φ y)) : M4aHerbrand.IdeleClassGroup (𝓞 K) K)) ∧
      Function.Injective ι.hom ∧
      (∀ c : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K),
        c ∈ Set.range ι.hom ↔ Additive.toMul c ∈
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).map
            (QuotientGroup.mk' (M4aHerbrand.principalIdeles (𝓞 K) K))) := by sorry
