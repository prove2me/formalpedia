-- Prove2me | Theorems.Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
-- name    : MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/eb1a4e31-492a-59e4-bd15-cbf0580cab75
-- title:
--   Bruhat section functions for a closed subgroup
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, assumed locally compact and second countable, and equipped with its Borel $\sigma$-algebra; let $T \le G$ be a subgroup whose underlying set is closed in $G$, itself regarded as a measurable space with the Borel structure of its subspace topology, and let $\tau$ be a measure on $T$ which is a Haar measure and is in addition invariant under right translations. Let $C \subseteq G$ be compact and let $E \subseteq G$ satisfy $E \subseteq T \cdot C = \{tc : t \in T,\ c \in C\}$ (the pointwise product of the underlying set of $T$ with $C$). The assertion is that there exists a function $w \colon G \to \mathbb{R}$ which is everywhere non-negative, Borel measurable, and of compact support (its topological support, the closure of $\{w \neq 0\}$, is compact), and which satisfies the normalisation $\int_T w(t x)\,\mathrm{d}\tau(t) = 1$ for every $x \in E$, the integral being the Bochner integral over $T$ of $t \mapsto w(tx)$ against $\tau$. Only measurability of $w$, not continuity, is asserted.
--
--   This is the existence of a section function (a "Bruhat function") for a set compact modulo the closed subgroup $T$: it allows integrals over the homogeneous space $T \backslash G$ of data supported on such a set to be expressed without constructing a quotient measure. It is used in the construction of orbital integrals at regular semisimple elements, where the orbit map is proper, and in the factorisation of orbital integrals over the adele ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

theorem MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    {E C : Set G} (hC : IsCompact C) (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by sorry
