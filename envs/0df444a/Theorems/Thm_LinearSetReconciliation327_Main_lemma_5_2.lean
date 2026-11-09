-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_2
-- name    : LinearSetReconciliation327.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:37.129271+00:00
-- url     : https://prove2.me/theorems/21f86699-7bb3-46b2-9b40-7bcfd6d0f969
-- title:
--   Lemma 5.2 — HintSketch abstention and incorrect prediction
-- statement:
--   At a recursive or direct node, for a regular row (row hint $J_j$ and support $S_j$ in $[N_j]$, $|J_j|\le B_X$, $y_j=|S_j\setminus J_j|\le B_Y$), after $a<\ell$ true recovered bits and over the row's coins: $\Pr[\text{worker returns }\bot]\le G_a(\sigma_{j,y_j}+c)$ and $\Pr[\text{incorrect prediction}]\le2^{-c}G_a(\sigma_{j,y_j}+c)$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - generalization: constants A, C fixed sufficiently large → all natural A, C; reason: the source proof uses only the row counts; the fixed constants are instances
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 5.2, PDF p.21 (printed p.20)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 5.2, PDF p.21 (printed p.20): for a regular row of a non-leaf node, after `a < ℓ` recovered
bits of the true transcript. The probability is over the coins of the row. -/
theorem lemma_5_2 (P : HintParams) (N X Y : ℕ) (hargs : P.NodeArgs N X Y) (hnl : P.NonLeaf N X Y)
    (j : Fin (P.rows X Y)) (Jj Sj : Finset ℕ)
    (hJj : Jj ⊆ range (rowLen N (P.rows X Y) j.val)) (hSj : Sj ⊆ range (rowLen N (P.rows X Y) j.val))
    (hreg : ¬ P.Overloaded N X Y Jj Sj) (a : Fin (P.ell N X Y)) :
    let sch := P.scheme N X Y
    let σ : ℝ := (HintParams.sigma Jj.card (rowLen N (P.rows X Y) j.val) (Sj \ Jj).card : ℝ)
    let c : ℝ := (P.c N X Y : ℝ)
    let q : sch.Rand → Option (ZMod 2) := fun β =>
      sch.predict j β Jj (sch.truePrefix j β Sj a.val)
    prU (fun β : sch.Rand => q β = none) ≤ G a.val (σ + c) ∧
    prU (fun β : sch.Rand => ∃ b, q β = some b ∧ b ≠ sch.code j β Sj a) ≤
      ((2 : ℝ) ^ (P.c N X Y))⁻¹ * G a.val (σ + c) := by sorry

end LinearSetReconciliation327.Main
