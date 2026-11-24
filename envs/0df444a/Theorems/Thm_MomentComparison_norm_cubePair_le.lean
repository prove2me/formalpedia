-- Prove2me | Theorems.Thm_MomentComparison_norm_cubePair_le
-- name    : MomentComparison.norm_cubePair_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:03:34.198682+00:00
-- url     : https://prove2.me/theorems/86ab4638-6684-4027-8e53-8d23c0940456
-- title:
--   Moment Comparison: norm cube Pair le
-- statement:
--   Hölder's inequality for the bilinear pairing under uniform cube probability.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Pairing.lean#L14-L34
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Pairing.lean#L14-L34

module
public import Definitions.Def_MomentComparison_MomentNorm
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Pairing
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison

theorem MomentComparison.norm_cubePair_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (f g : Cube n → ℂ) :
    ‖(∑ x, f x * g x) / (2 : ℂ) ^ n‖ ≤ complexMomentNorm p f * complexMomentNorm q g := by sorry
