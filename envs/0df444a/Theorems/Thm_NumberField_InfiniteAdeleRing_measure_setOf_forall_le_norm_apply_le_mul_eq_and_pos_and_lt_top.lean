-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_measure_setOf_forall_le_norm_apply_le_mul_eq_and_pos_and_lt_top
-- name    : NumberField.InfiniteAdeleRing.measure_setOf_forall_le_norm_apply_le_mul_eq_and_pos_and_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/13ce1ed1-4035-5d50-876d-049c13d96b25
-- title:
--   Haar measure of norm shells in K_∞^×
-- statement:
--   Let $K$ be a number field and let $K_\infty = \prod_{v \mid \infty} K_v$ be its infinite adele ring, the product of the completions of $K$ at its infinite places; the unit group $K_\infty^\times$ carries its Borel measurable structure, and $\nu$ is a Haar measure on it. Let $R$ be a real number with $1 < R$ and let $c = (c_v)_{v \mid \infty}$ be a family of reals with $c_v > 0$ for every infinite place $v$. For $p \in K_\infty^\times$ write $\|p_v\|$ for the norm of the $v$-component of the image of $p$ in $K_\infty$. The assertion is threefold: first, the $\nu$-measure of the shell $\{p : c_v \le \|p_v\| \le R\,c_v \text{ for all } v\}$ equals that of the normalised shell $\{p : 1 \le \|p_v\| \le R \text{ for all } v\}$; second, the measure of the normalised shell is strictly positive; third, it is strictly less than $\infty$.
--
--   This is the statement that the multiplicative norm shells in $K_\infty^\times$ all have one and the same finite, non-zero Haar volume, independent of the scaling family $c$. It underlies the normalisation "one shell per orbit" used in the construction of a measurable set on which an integral over the diagonal units is normalised to $1$, via [`AutomorphicForm.exists_measurable_forall_integral_toTensorGL_diagUnits2_mul_diagUnits2_eq_one`](thm.html#AutomorphicForm.exists_measurable_forall_integral_toTensorGL_diagUnits2_mul_diagUnits2_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_measure_setOf_forall_le_norm_apply_le_mul_eq_and_pos_and_lt_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.InfiniteAdeleRing.measure_setOf_forall_le_norm_apply_le_mul_eq_and_pos_and_lt_top
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ν : Measure (InfiniteAdeleRing K)ˣ) [ν.IsHaarMeasure]
    (R : ℝ) (hR : 1 < R) (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 < c v) :
    ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        c v ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R * c v} =
      ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        1 ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R} ∧
    0 < ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        1 ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R} ∧
    ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        1 ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R} < ⊤ := by sorry
