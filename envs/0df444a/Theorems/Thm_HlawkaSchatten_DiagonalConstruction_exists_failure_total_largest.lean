-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_failure_total_largest
-- name    : HlawkaSchatten.DiagonalConstruction.exists_failure_total_largest
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:26:21.061731+00:00
-- url     : https://prove2.me/theorems/4a2d29fb-9f3f-4d52-9dce-22e0811aaca6
-- title:
--   Relabeling a strict Hlawka failure so its total-sum size is largest
-- statement:
--   Let $\iota$ be a finite index set and, for a real exponent $p$, write $\|v\|_p := \big(\sum_{i\in\iota} |v_i|^p\big)^{1/p}$ for the coordinate power-sum functional of a real vector $v:\iota\to\mathbb R$, and call $\|v\|_p$ the *$p$-size* of $v$ (it is a norm for $p\ge1$; this argument does not use the triangle inequality). For real vectors $x,y,z:\iota\to\mathbb R$ and a real constant $K$, put
--
--   $$
--   S = \|x\|_p+\|y\|_p+\|z\|_p,\qquad T = \|x+y+z\|_p,\qquad P = \|x+y\|_p+\|x+z\|_p+\|y+z\|_p,
--   $$
--
--   and call $(x,y,z)$ a *strict Hlawka failure at level $K$* when
--
--   $$
--   (2K-1)S+T-KP<0;
--   $$
--
--   equivalently — since this quantity equals $K(2S-P)-(S-T)$ — when $(x,y,z)$ violates the inequality $S-T\le K(2S-P)$ that the construction seeks to establish.
--
--   Given $K\ge 1$ and a strict Hlawka failure $(x,y,z)$ at level $K$, this theorem produces a new triple $u,v,w:\iota\to\mathbb R$ that is again a strict Hlawka failure at level $K$, and for which the total-sum size dominates every individual size:
--
--   $$
--   \|u\|_p\le \|u+v+w\|_p,\qquad \|v\|_p\le \|u+v+w\|_p,\qquad \|w\|_p\le \|u+v+w\|_p.
--   $$
--
--   This is the relabeling step in normalizing a hypothetical counterexample to the diagonal Hlawka bound: among the four sizes $\|x\|_p,\|y\|_p,\|z\|_p,\|{-(x+y+z)}\|_p$ associated with the zero-sum quadruple $x,y,z,-(x+y+z)$, it arranges for the total-sum size $\|u+v+w\|_p$ to be at least each of the three retained singleton sizes, while preserving the fact that the relabeled triple is still a strict failure.
--
--   **Formalization Note** No hypothesis constrains the exponent $p$: the argument is a purely algebraic rearrangement of the four sizes and of the deficit quantity above, valid for every real $p$. Accordingly the $p$-size is an arbitrary power-sum functional here, not necessarily a norm.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Normalization.lean#L49-L81

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Abel

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Relabeling and normalization of a strict counterexample -/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.exists_failure_total_largest {p K : ℝ} (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by sorry
