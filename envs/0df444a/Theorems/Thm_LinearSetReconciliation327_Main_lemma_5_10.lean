-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_10
-- name    : LinearSetReconciliation327.Main.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:11.618315+00:00
-- url     : https://prove2.me/theorems/22fccdd4-ece4-4c54-be48-a5b432e7813c
-- title:
--   Lemma 5.10 — Size and depth of the recursion
-- statement:
--   There is an absolute $K$ such that for sufficiently large $A$, then $C$, and every node satisfying the standing assumptions, the recursion built from the stopping rules terminates and its tree has at most $K(\log\log n+1)$ levels, at most $K\log^{13}n$ recursive nodes and at most $KA\log^{27}n$ nodes in all.
--
--   Differences from the source:
--   - encoding: O-notation with absolute constants → explicit absolute constants and exponents quantified before all instance parameters; reason: §2.1: unless stated otherwise constants are absolute
--   - encoding: sufficiently large absolute A, then sufficiently large C → ∃A₀ ∀A≥A₀ ∃C₀ ∀C≥C₀, before the instance; reason: §5.2 fixes A first and then C
--   - encoding: O(log log n) levels → K(log log n + 1); reason: at n = 2, log log n = 0 while a tree has a level; the term 1 only makes the bound meaningful at finitely many small n
--   - encoding: the recursion is well founded (implicit) → the tree is built with fuel, and reaching a tree within the bound is a conclusion; reason: termination is part of what the lemma shows and is not assumed
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 5.10, PDF p.25 (printed p.24)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 5.10 (Size and depth of the recursion), PDF p.25 (printed p.24). The recursion terminates
within the stated number of levels, which is part of the conclusion. -/
theorem lemma_5_10 :
    ∃ K : ℝ, 0 < K ∧ ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y →
      ∃ (fuel : ℕ) (T : Node), P.tree fuel N X Y = some T ∧
        (fuel : ℝ) ≤ K * (lg (lg n) + 1) ∧
        (T.depth : ℝ) ≤ K * (lg (lg n) + 1) ∧
        (T.recursiveCount : ℝ) ≤ K * lg n ^ 13 ∧
        (T.nodeCount : ℝ) ≤ K * (A : ℝ) * lg n ^ 27 := by sorry

end LinearSetReconciliation327.Main
