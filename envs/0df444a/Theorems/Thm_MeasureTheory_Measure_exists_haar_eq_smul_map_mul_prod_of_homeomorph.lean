-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph
-- name    : MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/8e2b8211-48ee-5112-9dbd-46e5890c8330
-- title:
--   Haar measure of a bi-invariant group factorised as T· S
-- statement:
--   Let $G$ be a group carrying a topology making it a Hausdorff, locally compact, second countable topological group, equipped with its Borel $\sigma$-algebra, and let $T,S\le G$ be subgroups, each equipped with a measurable structure which is its Borel structure. Suppose given a homeomorphism $e\colon T\times S\to G$ which, as a function, is the multiplication map, i.e. $e(t,s)=t\,s$ in $G$ for all $(t,s)$. Let $\mu$ be a measure on $G$ that is a left Haar measure (left invariant, finite on compacts, positive on nonempty opens, in the Mathlib sense) and in addition right invariant; let $\tau$ be a left Haar measure on $T$; and let $\nu$ be a measure on $S$ which is finite on compact sets, right invariant and positive on nonempty open sets. Then there exists a constant $c\in[0,\infty]$ with $c\neq 0$ and $c\neq\infty$ such that $\mu = c\cdot e_*(\tau\otimes\nu)$, the pushforward along $e$ of the product measure $\tau\otimes\nu$ scaled by $c$.
--
--   This is the classical computation of Haar measure on a group which factors topologically as a product of two subgroups, in the case where the ambient measure is bi-invariant (in general the modular functions of $G$ and $S$ intervene). It is used in the analytic side of the argument, to rewrite integrals over $G$ as iterated integrals over the two factors, and is cited by [`AutomorphicForm.integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero`](thm.html#AutomorphicForm.integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T S : Subgroup G) [MeasurableSpace T] [BorelSpace T] [MeasurableSpace S] [BorelSpace S]
    (e : T × S ≃ₜ G) (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (τ : Measure T) [τ.IsHaarMeasure]
    (ν : Measure S) [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant] [ν.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map e (τ.prod ν) := by sorry
