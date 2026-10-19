-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_real_three_window26
-- name    : HlawkaSchatten.DiagonalCutoff21.real_three_window26
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T08:14:55.917535+00:00
-- url     : https://prove2.me/theorems/a1a7a36f-f8b9-4061-84a2-33080e185b41
-- title:
--   Real three-dimensional Hlawka admissibility on [26, 32]
-- statement:
--   For each real exponent p in the closed interval [26,32] and all real three-coordinate vectors x,y,z, their triple norm deficit is at most K_p times the sum of their three pair norm deficits. K_p and lpNorm are the unchanged campaign definitions. The conclusion covers all triples, including unequal norms and zero vectors, with no localization, normalization, certificate-validity or convexity assumption.
-- source:
--   Yuxuan Xu (徐宇轩), School of Computer Science, Wuhan University. A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1, 17 October 2026. https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.pdf . LaTeX: https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.tex . Reproducibility: https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/results/release-replay.json . AI-assisted research preprint; independent analytic review pending; no new Lean proof. Section 7, paragraph following equation (40): exclusion of all real three-dimensional counterexamples on Window II. Sections 3-6 and Lemma 8.1 supply the argument.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.real_three_window26 :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
