-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window21
-- name    : HlawkaSchatten.DiagonalCutoff21.scalar_window21
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T08:14:14.627991+00:00
-- url     : https://prove2.me/theorems/2b5def5c-82ab-4480-bbcb-1d11f05b7cbe
-- title:
--   Scalar bounds on the full real window [21, 26]
-- statement:
--   For every real p in the closed interval [21,26], c p < K_p, K_p <= p/2, and E_p(q) < K_p, where c=273/625, q=1011/2500, K_p is the unchanged foundation cyclic maximum, and E_p(q)=(1-q)/(2(1-((1+q^p)/2)^(1/p))). No numerical certificate hypothesis or sampled-exponent restriction is assumed.
-- source:
--   Yuxuan Xu (徐宇轩), School of Computer Science, Wuhan University. A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1, 17 October 2026. https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.pdf . LaTeX: https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.tex . Reproducibility: https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/results/release-replay.json . AI-assisted research preprint; independent analytic review pending; no new Lean proof. Section 3, equation (7), Table 1, Window I; finite certificate specification in Lemma 8.1.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.scalar_window21 :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
      (273 / 625 : ℝ) * p < cyclicConstant p ∧
      cyclicConstant p ≤ p / 2 ∧
      scalarEnvelope p (1011 / 2500 : ℝ) < cyclicConstant p := by sorry
