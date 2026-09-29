-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_lpNorm_le_card_root_mul
-- name    : HlawkaSchatten.DiagonalConstruction.lpNorm_le_card_root_mul
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:11:32.305991+00:00
-- url     : https://prove2.me/theorems/24a242d0-b516-4218-8a0f-a615fb4f5fa1
-- title:
--   A uniform coordinate bound for the finite $p$-norm
-- statement:
--   Let $\iota$ be a finite index set, $E$ a normed additive group, $p>0$ a real exponent, and $M\ge0$ a real number. For $x=(x_i)_{i\in\iota}$ with $\|x_i\|\le M$ at every index $i$, the coordinate $p$-norm
--
--   $$
--   \mathrm{lpNorm}_p(x)=\Big(\sum_{i\in\iota}\|x_i\|^p\Big)^{1/p}
--   $$
--
--   satisfies
--
--   $$
--   \mathrm{lpNorm}_p(x) \;\le\; |\iota|^{1/p}\, M,
--   $$
--
--   where $|\iota|$ is the cardinality of $\iota$.
--
--   This turns a uniform bound on every individual coordinate into a bound on the whole vector's $p$-norm, with the cardinality factor $|\iota|^{1/p}$ that is exactly attained when every coordinate saturates the bound $M$. It belongs to the same foundational layer of coordinate-norm bounds as positive-definiteness and, once $p\ge1$, the triangle inequality for $\mathrm{lpNorm}_p$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Basic.lean#L109-L122

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/


variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by sorry
