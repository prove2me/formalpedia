-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk02
-- name    : HlawkaSchatten.DiagonalCutoff21.lower21_chunk02
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:25:39.471841+00:00
-- url     : https://prove2.me/theorems/2c97328b-bb23-41d7-909f-9b645327ded4
-- title:
--   Fixed cyclic witness: Kp > (273/625)p for real p in [22,45/2]
-- statement:
--   For every real $p\in[22,45/2]$, the cyclic Hlawka constant satisfies $(273/625)p<K_p$. Here $K_p$ is the source paper's supremum of the cyclic ratio over $1/2\le t\le2$. The same fixed rational witness $t=17/20$ works on the entire interval, which contains sixteen adjacent closed subintervals. This is a lower-bound component of the scalar-window target, with no numerical-check predicate as a hypothesis.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 2, equation (7), linear lower-bound component. Fixed-witness Bernoulli proof and exact certificates: certificates/lean-scalar-cutoff21.json, slabs 32 through 47.

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.lower21_chunk02 (p : ℝ) (hpa : (22 : ℝ) ≤ p) (hpb : p ≤ (45/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by sorry
