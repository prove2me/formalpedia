-- Prove2me | Theorems.Thm_MeasureTheory_exists_continuous_integral_subgroup_mul_eq_one
-- name    : MeasureTheory.exists_continuous_integral_subgroup_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/3f3e6877-3d8a-5895-9504-54f87ed74c91
-- title:
--   Continuous cut-off with T-orbit integral one on a compact set
-- statement:
--   Let $G$ be a group carrying a topology making it a locally compact Hausdorff topological group whose topology is first countable. Let $T$ be a subgroup of $G$ whose underlying set is closed in $G$ and which is commutative in the sense that $st = ts$ for all $s, t \in T$; equip $T$ with a measurable space structure which is the Borel structure of its subspace topology, and let $\tau$ be a Haar measure on $T$. Let $\Omega \subseteq G$ be compact. The assertion is that there exists a function $w : G \to \mathbb{R}$ which is continuous, pointwise non-negative and has compact support, such that for every $x \in G$ admitting a factorisation $x = t d$ with $t \in T$ and $d \in \Omega$, one has $\int_{T} w(t x) \, d\tau(t) = 1$. Note that the normalisation is required only at points of the set $T \cdot \Omega$, and that no condition is imposed on $w$ elsewhere; in particular the degenerate case $\Omega = \emptyset$ is included, where the zero function qualifies.
--
--   This is the standard existence of a continuous compactly supported cut-off function whose integral along the orbits of a closed subgroup is normalised to $1$ on a prescribed compact set, the continuous counterpart of the locally constant cut-offs used to normalise quotient measures. It is used in the construction of archimedean test functions for twisted orbital integrals of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_continuous_integral_subgroup_mul_eq_one.lean

import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

universe u

theorem MeasureTheory.exists_continuous_integral_subgroup_mul_eq_one
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [FirstCountableTopology G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : G, (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) → ∫ t : T, w (t * x) ∂τ = 1 := by sorry
