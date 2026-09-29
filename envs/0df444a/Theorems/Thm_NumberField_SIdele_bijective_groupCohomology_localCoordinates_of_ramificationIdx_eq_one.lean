-- Prove2me | Theorems.Thm_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
-- name    : NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/b7c0d1e5-7f87-5e9b-b7f7-e160eac43b54
-- title:
--   Semilocal description of S-idèle cohomology in positive degree
-- statement:
--   Let $E \subseteq K$ be number fields with $K$ Galois over $E$, with group $G = \mathrm{Gal}(K/E)$, let $S$ be a finite set of height-one primes of $\mathcal O_E$, and assume that every height-one prime $w$ of $\mathcal O_K$ whose contraction $w \cap \mathcal O_E$ does not lie in $S$ satisfies $e(w \mid w \cap \mathcal O_E) = 1$. Let $n$ be a natural number. The $S$-idèle module is the $\mathbb Z[G]$-representation given by the product, over the index type $(\{v \in S\} \sqcup \{v \notin S\}) \sqcup \{\text{infinite places of } E\}$, of the coinduced representations $\mathrm{Coind}_{D_{w(v)}}^{G} K_{w(v)}^\times$ for $v \in S$, $\mathrm{Coind}_{D_{w(v)}}^{G} \mathcal O_{w(v)}^\times$ for $v \notin S$, and $\mathrm{Coind}_{D_{w(v)}}^{G} (K_{w(v)})^\times$ for $v$ infinite, where $w(v)$ is in each case the chosen place of $K$ above $v$ and $D_{w(v)}$ its decomposition subgroup. The assertion is that the map from $H^{n+1}(G, \cdot)$ of this product to $$\textstyle\prod_{v \in S} H^{n+1}(D_{w(v)}, K_{w(v)}^\times) \times \prod_{v \mid \infty} H^{n+1}(D_{w(v)}, K_{w(v)}^\times),$$ whose coordinate at $v$ is cohomology of the projection onto the factor at $v$ followed by Shapiro's isomorphism for coinduced modules, is bijective. The coordinates at the primes outside $S$ do not appear in the target.
--
--   This is the semilocal description of the cohomology of the $S$-idèles: in degrees $\ge 1$, and under the hypothesis that $K/E$ is unramified outside $S$, the cohomology of the $S$-idèle module is the product of the local cohomology groups at the places in $S$ and at the archimedean places. It is used in the Herbrand-quotient and level-arithmetic computations that feed the global class-field-theoretic input of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (n : ℕ) :
    Function.Bijective (fun x : groupCohomology (NumberField.SIdele.obj E K S) (n + 1) =>
      ((fun v : {v // v ∈ S} =>
          (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
              (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) (n + 1) ≫
            (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) (n + 1)).hom).hom x),
       (fun v : InfinitePlace E =>
          (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
              (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inr v)) (n + 1) ≫
            (groupCohomology.coindIso (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)) (n + 1)).hom).hom x))) := by sorry
