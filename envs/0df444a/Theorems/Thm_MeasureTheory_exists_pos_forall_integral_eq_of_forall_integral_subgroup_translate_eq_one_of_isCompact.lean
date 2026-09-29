-- Prove2me | Theorems.Thm_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
-- name    : MeasureTheory.exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/5855b876-65f8-53cd-a49e-ccf2868d18dd
-- title:
--   Covolume of a cocompact closed subgroup via section functions
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, locally compact, second countable, with its Borel measurable structure, let $T\le G$ be a subgroup whose underlying set is closed in $G$ (again with its Borel structure), let $\mu$ be a Haar measure on $G$ and $\tau$ a Haar measure on $T$ that is moreover invariant under inversion, and suppose there is a compact set $C\subseteq G$ with $G=T\cdot C$, i.e. every $g\in G$ can be written as $g=t k$ with $t\in T$ and $k\in C$. The conclusion asserts the existence of a real number $\kappa>0$ with two properties. First, there exists a function $w\colon G\to\mathbb{R}$ that is non-negative everywhere, continuous, of compact support, and satisfies $\int_T w(tx)\,d\tau(t)=1$ for every $x\in G$. Second, for every $w\colon G\to\mathbb{R}$ which is non-negative, measurable and of compact support and satisfies $\int_T w(tx)\,d\tau(t)=1$ for all $x\in G$, one has $\int_G w\,d\mu=\kappa$. Thus the common value of $\int_G w\,d\mu$ over all such "section functions" for $T\backslash G$ is a single positive constant, and the family of such functions is non-empty; no quotient measure on $T\backslash G$ is constructed.
--
--   The constant $\kappa$ is the covolume of the cocompact closed subgroup $T$ in $G$ with respect to $\mu$ and $\tau$, expressed through section functions rather than through a measure on the quotient $T\backslash G$. It is used in the archimedean analysis of twisted orbital integrals, being cited in the proof of [`AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer`](thm.html#AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (C : Set G) (hC : IsCompact C) (hcov : ∀ g : G, ∃ t : T, ∃ k ∈ C, g = (t : G) * k) :
    ∃ κ : ℝ, 0 < κ ∧
      (∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Continuous w ∧ HasCompactSupport w ∧
        ∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∀ w : G → ℝ, (∀ x, 0 ≤ w x) → Measurable w → HasCompactSupport w →
        (∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) → ∫ x, w x ∂μ = κ := by sorry
