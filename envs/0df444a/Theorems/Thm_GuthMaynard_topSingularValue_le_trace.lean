-- Prove2me | Theorems.Thm_GuthMaynard_topSingularValue_le_trace
-- name    : GuthMaynard.topSingularValue_le_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:11:45.787039+00:00
-- url     : https://prove2.me/theorems/4f3c4e3d-5f22-4e0e-9d41-a172db6e4dd4
-- title:
--   Lemma 4.2 (Bound for singular values in terms of traces)
-- statement:
--   For every complex matrix $A$ with $m$ rows (indexed by a finite type),
--   $$s_1(A) \le 2\Big(\operatorname{Re}\operatorname{tr}\big((AA^*)^3\big) - \frac{(\operatorname{Re}\operatorname{tr}(AA^*))^3}{m^2}\Big)^{1/6} + 2\Big(\frac{\operatorname{Re}\operatorname{tr}(AA^*)}{m}\Big)^{1/2},$$
--   where $s_1(A)$ is the largest singular value (`topSingularValue A`) and powers are real powers (`Real.rpow`).
--
--   **Formalization note.** The traces of $AA^*$ and $(AA^*)^3$ are real; the statement takes their real parts. The bracket in the first term is nonnegative (that is the Hölder step of the proof), so its sixth root is the ordinary one.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 12, Lemma 4.2 (Bound for singular values in terms of traces)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem topSingularValue_le_trace {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) :
    topSingularValue A ≤
      2 * (((A * A.conjTranspose) ^ 3).trace.re -
          (A * A.conjTranspose).trace.re ^ 3 / (Fintype.card ι : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
        2 * ((A * A.conjTranspose).trace.re / Fintype.card ι) ^ (1 / 2 : ℝ) := by
  sorry

end GuthMaynard
