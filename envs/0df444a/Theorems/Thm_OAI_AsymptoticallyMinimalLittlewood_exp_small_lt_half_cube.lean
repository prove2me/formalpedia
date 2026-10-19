-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exp_small_lt_half_cube
-- name    : OAI.AsymptoticallyMinimalLittlewood.exp_small_lt_half_cube
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:43:12.644986+00:00
-- url     : https://prove2.me/theorems/8f418d46-5ad4-4376-8321-1de573f10f67
-- title:
--   The inequality $e^{13n/32}<2^{n}/2$ for all $n\ge 32$
-- statement:
--   For every natural number $n\ge32$,
--
--   $$
--   e^{13n/32}<\frac{2^{n}}{2}.
--   $$
--
--   In the partial-coloring argument the set of signings with small rounding cost has at least $2^n/2$ elements, while the entropy bounds for the number of codes and the size of Hamming balls multiply to at most $e^{13n/32}$; this inequality is what forces two far-apart signings with the same code to exist.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L399-L416

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.exp_small_lt_half_cube {n : ℕ} (hn : 32 ≤ n) :
    Real.exp (13 * n / 32) < (2 : ℝ) ^ n / 2 := by sorry
