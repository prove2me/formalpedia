-- Prove2me | Theorems.Thm_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le
-- name    : IsLocalRing.mk_comp_algebraMap_surjective_of_maximalIdeal_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/6dd77bea-a2ec-5fd8-b568-6293ffe8b5d1
-- title:
--   Surjectivity of 𝒪 → A/J from relative cotangent generation
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring which is precomplete for its maximal ideal $\mathfrak{m}_{\mathcal{O}}$ (every Cauchy sequence for the $\mathfrak{m}_{\mathcal{O}}$-adic filtration has a limit, with no uniqueness of limits assumed), and let $A$ be a noetherian local commutative $\mathcal{O}$-algebra. Assume that the composite of the structure map $\mathcal{O} \to A$ with the residue map $A \to A/\mathfrak{m}_A$ is surjective, and let $J$ be an ideal of $A$ such that $$\mathfrak{m}_A \subseteq J + \mathfrak{m}_A^2 + \mathfrak{m}_{\mathcal{O}}A,$$ where $\mathfrak{m}_{\mathcal{O}}A$ denotes the image ideal of $\mathfrak{m}_{\mathcal{O}}$ under $\mathcal{O} \to A$; equivalently, the image of $J$ spans the relative cotangent space $\mathfrak{m}_A/(\mathfrak{m}_A^2 + \mathfrak{m}_{\mathcal{O}}A)$. Then the composite $\mathcal{O} \to A \to A/J$ is surjective. No inclusion $J \subseteq \mathfrak{m}_A$ is hypothesised: the case $J = A$ is degenerate and otherwise the inclusion is automatic. The hypothesis on $A$ is that of a noetherian ring; no completeness of $A$ is assumed, only precompleteness of the base $\mathcal{O}$.
--
--   This is the relative, topological form of Nakayama's lemma for the structure map of a local algebra over a precomplete local base: generation of the relative cotangent space by an ideal $J$ forces $\mathcal{O}$ to surject onto $A/J$. It is the substantive input to the generator-count theorem stating that a complete noetherian local $\mathcal{O}$-algebra whose relative cotangent space is spanned by $r$ elements is a quotient of a power series ring in $r$ variables over $\mathcal{O}$, which is the bound used when presenting universal deformation rings; the statement [`IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span`](thm.html#IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span) consumes it directly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le.lean

import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem IsLocalRing.mk_comp_algebraMap_surjective_of_maximalIdeal_le
    {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsPrecomplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A]
    (hres : Function.Surjective (⇑(IsLocalRing.residue A) ∘ ⇑(algebraMap 𝒪 A)))
    {J : Ideal A}
    (hle : IsLocalRing.maximalIdeal A ≤
      J ⊔ IsLocalRing.maximalIdeal A ^ 2 ⊔ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    Function.Surjective (⇑(Ideal.Quotient.mk J) ∘ ⇑(algebraMap 𝒪 A)) := by sorry
