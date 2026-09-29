-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
-- name    : HlawkaSchatten.DiagonalConstruction.exists_normalized_failure
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:29:33.759583+00:00
-- url     : https://prove2.me/theorems/5cabcd82-b2e4-4eed-bc12-e20c4c8eaae0
-- title:
--   Normalizing a strict Hlawka failure to unit norm-sum
-- statement:
--   Let $\iota$ be a finite index set and, for a real exponent $p>0$, write $\|v\|_p:=\big(\sum_{i\in\iota}|v_i|^p\big)^{1/p}$ for a real vector $v:\iota\to\mathbb R$. For $x,y,z:\iota\to\mathbb R$ and $K\in\mathbb R$, set $S=\|x\|_p+\|y\|_p+\|z\|_p$, $T=\|x+y+z\|_p$, $P=\|x+y\|_p+\|x+z\|_p+\|y+z\|_p$, and call $(x,y,z)$ a *strict Hlawka failure at level $K$* when $(2K-1)S+T-KP<0$, equivalently $S-T>K(2S-P)$.
--
--   Given $p>0$, $K\ge1$, and a strict Hlawka failure $(x,y,z)$ at level $K$ — with no further hypothesis on $(x,y,z)$ — this theorem produces a new triple $u,v,w:\iota\to\mathbb R$ that is again a strict Hlawka failure at level $K$, for which the singleton norms sum to exactly one, and for which the total-sum norm dominates each singleton norm:
--
--   $$
--   \|u\|_p+\|v\|_p+\|w\|_p = 1,\qquad \|u\|_p\le\|u+v+w\|_p,\qquad \|v\|_p\le\|u+v+w\|_p,\qquad \|w\|_p\le\|u+v+w\|_p.
--   $$
--
--   This produces, from an arbitrary strict counterexample, a canonically scaled one — normalized to unit singleton-norm sum and with total-norm domination — that fixes the scale used throughout the later scalar and coordinate estimates confining a hypothetical counterexample to the sharp diagonal Hlawka inequality.
--
--   **Formalization Note** For $0<p<1$ the triangle inequality can fail; the argument uses only positive-definiteness and positive homogeneity, which hold for every $p>0$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Normalization.lean#L104-L125

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

theorem HlawkaSchatten.DiagonalConstruction.exists_normalized_failure {p K : ℝ} (hp : 0 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u + lpNorm p v + lpNorm p w = 1 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by sorry
