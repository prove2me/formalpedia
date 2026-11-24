-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagMonotoneEqContPlusPosJumpTsumV1
-- name    : Kyprianou.Ch02.cadlagMonotoneEqContPlusPosJumpTsumV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:27:54.766197+00:00
-- url     : https://prove2.me/theorems/b488a343-8065-4a0c-81c4-974c950d3847
-- title:
--   C\`adl\`ag monotone path equals continuous residual plus positive jump sum
-- statement:
--   Let $f:\mathbb{R}_{\ge 0}\to\mathbb{R}$ be a c\`adl\`ag monotone path. Write
--   $$
--   J_t=\sum_{0<s\le t}\max\bigl(f(s)-f(s-),0\bigr)
--   $$
--   for the cumulative sum of its positive jumps (left limits taken along $(0,s)$). Then the residual
--   $$
--   C_t=f(t)-J_t
--   $$
--   is continuous and monotone.
--
--   This is the classical pathwise Jordan/Stieltjes decomposition of an increasing c\`adl\`ag trajectory into a continuous increasing part and a pure-jump part; it is the deterministic ingredient in the Lévy-subordinator drift-plus-jump identity of Kyprianou, Chapter 2.
--
--   **Formalization Note.** Left limits are expressed as `Filter.limUnder (nhdsWithin s (Set.Iio s)) f`, matching the jump convention used throughout the Chapter 2 BV Lévy formalization.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes with Applications, Springer 2014, Chapter 2 (subordinators / Lévy-Itô for increasing processes), cf. Theorem 2.8 and surrounding discussion of continuous vs jump parts.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagMonotoneEqContPlusPosJumpTsumV1
    (f : ℝ≥0 → ℝ)
    (hf : ProbabilityTheory.IsCadlag f)
    (hm : Monotone f) :
    Continuous (fun t : ℝ≥0 =>
      f t - ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (f s.1 - Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) f) 0) ∧
    Monotone (fun t : ℝ≥0 =>
      f t - ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (f s.1 - Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) f) 0) := by sorry
