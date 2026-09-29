-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_lpNorm_eq_zero_iff
-- name    : HlawkaSchatten.DiagonalConstruction.lpNorm_eq_zero_iff
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:38:05.514356+00:00
-- url     : https://prove2.me/theorems/a6e183df-2e12-4a8f-8c7c-060792b3bb47
-- title:
--   Positive-definiteness of the finite coordinate $p$-norm
-- statement:
--   Fix a finite index set $\iota$ and a normed additive group $E$. For a real exponent $p>0$ and a vector $x=(x_i)_{i\in\iota}$ with each $x_i\in E$, define the coordinate $p$-norm
--
--   $$
--   \mathrm{lpNorm}_p(x) \;=\; \Big(\sum_{i\in\iota}\|x_i\|^{p}\Big)^{1/p}.
--   $$
--
--   The theorem states that, for every $p>0$,
--
--   $$
--   \mathrm{lpNorm}_p(x)=0 \iff x=0,
--   $$
--
--   where $0$ denotes the vector sending every index to the zero element of $E$.
--
--   This is the positive-definiteness axiom for the explicit finite power-sum functional $\mathrm{lpNorm}_p$ used throughout the diagonal Schatten construction, and it holds for every exponent $p>0$.
--
--   **Formalization Note** For $p\ge1$, $\mathrm{lpNorm}_p$ satisfies the triangle inequality and is a norm. This theorem's positive-definiteness holds more broadly, for every $p>0$; by itself it does not make $\mathrm{lpNorm}_p$ a norm outside that range. The result holds independently of the exponent-indexed `PiLp` type that Mathlib uses to package $\ell^p$-type norms.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Basic.lean#L61-L73

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

theorem HlawkaSchatten.DiagonalConstruction.lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by sorry
