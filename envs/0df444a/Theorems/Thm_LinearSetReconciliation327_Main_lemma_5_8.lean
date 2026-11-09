-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_8
-- name    : LinearSetReconciliation327.Main.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:49.598173+00:00
-- url     : https://prove2.me/theorems/d8d99f09-5c84-401d-a1d1-09152bfbdbda
-- title:
--   Lemma 5.8 — Outside-hint charge
-- statement:
--   For sufficiently large $A$, then $C$, at a recursive node, $\sum_{s=1}^\ell h_Y(2^{-c}Q_s)\le h_N(Y)/8$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: sufficiently large absolute A, then sufficiently large C → ∃A₀ ∀A≥A₀ ∃C₀ ∀C≥C₀, before the instance; reason: §5.2 fixes A first and then C
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 5.8, PDF p.23 (printed p.22)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 5.8, PDF p.23 (printed p.22). `A`, then `C`, are sufficiently large. -/
theorem lemma_5_8 :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∑ s ∈ range (P.ell N X Y), hN Y (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s) ≤ hN N Y / 8 := by sorry

end LinearSetReconciliation327.Main
