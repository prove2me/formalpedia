-- Prove2me | Theorems.Thm_Kac_toENNReal_eq_tsum
-- name    : Kac.toENNReal_eq_tsum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:07:44.900678+00:00
-- url     : https://prove2.me/theorems/7bef83be-b6cd-4844-a202-597231279421
-- title:
--   Kac: to ENNReal eq tsum
-- statement:
--   The tail-sum formula on `ℕ∞`: `k = ∑ₙ [n < k]`, including `k = ⊤`.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L165-L179
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L165-L179

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}

theorem Kac.toENNReal_eq_tsum (k : ℕ∞) :
    (k : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < k then 1 else 0 := by sorry
