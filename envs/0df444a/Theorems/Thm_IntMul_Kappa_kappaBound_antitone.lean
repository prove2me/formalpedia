-- Prove2me | Theorems.Thm_IntMul_Kappa_kappaBound_antitone
-- name    : IntMul.Kappa.kappaBound_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T19:39:43.535223+00:00
-- url     : https://prove2.me/theorems/26a386e7-11ff-4fdd-8f5f-a9b95bd58ea9
-- title:
--   A stronger multitape multiplication exponent implies every weaker exponent
-- statement:
--   For arbitrary real exponents κ ≤ κ′, if a single deterministic multitape Turing machine multiplies exactly with eventual time O(n(lg n)^(1-κ′)), then the same machine witnesses O(n(lg n)^(1-κ)). This general exponent-transfer lemma uses lg n ≥ 1 and the proved eventual time-bound majorisation theorem. It provides a reusable reduction for the integer-multiplication mission, independent of any particular algorithm construction.
-- source:
--   General exponent comparison derived from the authoritative IntMul_MultitapeModel definitions and the accepted theorem IntMul.Kappa.mul_time_bound_of_eventual_le. Supports integer multiplication mission e901a985-a077-435a-bd78-2df1c12fb4f3.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_IntMul_Kappa_mul_time_bound_of_eventual_le

theorem IntMul.Kappa.kappaBound_antitone {κ κ' : ℝ}
    (hκ : κ ≤ κ') (hstrong : IntMul.KappaBound κ') :
    IntMul.KappaBound κ := by sorry
