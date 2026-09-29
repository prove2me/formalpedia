-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain
-- name    : MeasureTheory.Measure.exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/580bbc8e-0436-5c99-a73b-dd3e9fb0455d
-- title:
--   Pushforward of Haar measure on a fundamental domain
-- statement:
--   Let $G$ be a commutative topological group that is locally compact, $\sigma$-compact, and equipped with its Borel $\sigma$-algebra, and let $H$ be a commutative, Hausdorff, locally compact topological group, likewise with the Borel $\sigma$-algebra; let $\mu$ be a Haar measure on $G$ and $\nu$ a Haar measure on $H$. Let $f \colon G \to H$ be a continuous group homomorphism whose range $f(G)$ is open in $H$. Let $\Gamma$ be a countable subgroup of $G$ contained in $\ker f$, and assume that $\ker f$ is covered by $\Gamma \cdot D$ for some compact set $D \subseteq G$, the product being taken pointwise in $G$. Let $\Theta \subseteq G$ be a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the translation action of $\Gamma$ on $G$ with respect to $\mu$. The conclusion is the existence of a real number $\kappa > 0$ such that the pushforward along $f$ of the restriction $\mu|_{\Theta}$ equals $\mathrm{ofReal}(\kappa)$ times the restriction $\nu|_{f(G)}$, as measures on $H$.
--
--   This is Weil's formula for integration along the fibres of $f$, stated as an identity of measures: the image of Haar measure on a fundamental domain for a cocompact countable subgroup of $\ker f$ is a positive multiple of Haar measure on the open subgroup $f(G)$. It is used in the construction of Haar measure on the idele class group and in the resulting comparison of integrals of functions of the idelic norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

theorem MeasureTheory.Measure.exists_map_restrict_eq_smul_restrict_range_of_isFundamentalDomain
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (Γ : Subgroup G) [Countable Γ] (hΓ : Γ ≤ f.ker)
    (hker : ∃ D : Set G, IsCompact D ∧ (f.ker : Set G) ⊆ (Γ : Set G) * D)
    (Θ : Set G) (hΘ : IsFundamentalDomain Γ Θ μ) :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map f (μ.restrict Θ) = ENNReal.ofReal κ • ν.restrict (Set.range f) := by sorry
