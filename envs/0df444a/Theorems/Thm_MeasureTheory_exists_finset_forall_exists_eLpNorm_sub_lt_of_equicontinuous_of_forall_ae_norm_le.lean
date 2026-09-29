-- Prove2me | Theorems.Thm_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
-- name    : MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/f7f3cf59-eebd-5919-b56c-d996ca1e960a
-- title:
--   Arzelà–Ascoli in Lᵖ: finite ε-nets for equicontinuous families
-- statement:
--   Let $X$ be a Hausdorff topological space carrying a measurable structure for which open sets are measurable, let $E$ be a normed additive commutative group whose underlying metric space is proper (closed bounded sets are compact), and let $u : \iota \to X \to E$ be a family of functions indexed by an arbitrary type $\iota$. Let $\mu$ be a finite measure on $X$ and let $p \in [0,\infty]$ satisfy $1 \le p$ and $p \neq \infty$. Assume: (i) $\mu$ is tight, in the sense that for every $\eta > 0$ in $[0,\infty]$ there is a compact $K \subseteq X$ with $\mu(K^{c}) < \eta$; (ii) the family $u$ is equicontinuous; (iii) it is pointwise bounded, i.e. for each $x \in X$ there is a real $C_0$ with $\|u_i(x)\| \le C_0$ for all $i$; (iv) there is a real $C$ such that for each $i$ one has $\|u_i(x)\| \le C$ for $\mu$-almost every $x$. Then for every $\varepsilon > 0$ in $[0,\infty]$ there is a finite subset $s$ of $\iota$ such that every index $i$ admits some $j \in s$ with $\mathrm{eLpNorm}(u_i - u_j, p, \mu) < \varepsilon$. Thus the family is totally bounded for the $L^p$-seminorm, at the level of functions rather than of classes.
--
--   This is the $L^p$ form of the Arzelà–Ascoli theorem: equicontinuity plus pointwise and almost-everywhere uniform bounds, together with tightness of a finite measure, give finite $\varepsilon$-nets for the $L^p$-seminorm. It is the analytic input used in establishing that the smoothing operators on the cuspidal spectrum are compact.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Topology Filter Set BoundedContinuousFunction
open scoped ENNReal NNReal

theorem MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {ι : Type*} (u : ι → X → E) (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp : p ≠ ∞)
    (htight : ∀ η : ℝ≥0∞, 0 < η → ∃ K : Set X, IsCompact K ∧ μ Kᶜ < η)
    (hequi : Equicontinuous u)
    (hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀)
    (C : ℝ) (hbound : ∀ i, ∀ᵐ x ∂μ, ‖u i x‖ ≤ C)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ i, ∃ j ∈ s, eLpNorm (u i - u j) p μ < ε := by sorry
