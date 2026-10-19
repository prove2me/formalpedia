-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower26_chunk05
-- name    : HlawkaSchatten.DiagonalCutoff21.lower26_chunk05
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:25:39.453395+00:00
-- url     : https://prove2.me/theorems/67ac9418-5152-410a-af89-3bf6e35b5f0f
-- title:
--   Fixed cyclic witness: Kp > (443/1000)p for real p in [31,32]
-- statement:
--   For every real $p\in[31,32]$, the cyclic Hlawka constant satisfies $(443/1000)p<K_p$. Here $K_p$ is the source paper's supremum of the cyclic ratio over $1/2\le t\le2$. The same fixed rational witness $t=87/100$ works on the entire interval, which contains sixteen adjacent closed subintervals. This is a lower-bound component of the scalar-window target, with no numerical-check predicate as a hypothesis.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 2, equation (7), linear lower-bound component. Fixed-witness Bernoulli proof and exact certificates: certificates/lean-scalar-cutoff26.json, slabs 80 through 95.

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

theorem HlawkaSchatten.DiagonalCutoff21.lower26_chunk05 (p : ℝ) (hpa : (31 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by sorry
