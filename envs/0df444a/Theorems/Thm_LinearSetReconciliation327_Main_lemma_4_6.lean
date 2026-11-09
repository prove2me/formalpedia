-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_6
-- name    : LinearSetReconciliation327.Main.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:43.71747+00:00
-- url     : https://prove2.me/theorems/fdaf70d4-28ec-4b11-82ff-3cfa253b498d
-- title:
--   Lemma 4.6 — Summing prefix tails
-- statement:
--   There is one absolute constant $C$ such that for all real $z\ge0$, $\sum_{a\ge0}G_a(z)\le z+C$ and $\sum_{a\ge0}aG_a(z)\le C(1+z)^2$, both as extended nonnegative sums.
--
--   Differences from the source:
--   - encoding: real infinite sums → extended nonnegative sums; reason: summands are nonnegative, so a real tsum junk value is avoided
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 4.6, PDF p.17 (printed p.16)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 4.6 (Summing prefix tails), PDF p.17 (printed p.16): one absolute `C`, both sums over all
`a ≥ 0`, as extended nonnegative sums. -/
theorem lemma_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 ≤ z →
      (∑' a : ℕ, ENNReal.ofReal (G a z)) ≤ ENNReal.ofReal (z + C) ∧
      (∑' a : ℕ, ENNReal.ofReal ((a : ℝ) * G a z)) ≤ ENNReal.ofReal (C * (1 + z) ^ 2) := by sorry

end LinearSetReconciliation327.Main
