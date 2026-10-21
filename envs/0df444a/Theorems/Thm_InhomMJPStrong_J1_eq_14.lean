-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_eq_14
-- name    : InhomMJPStrong.J1.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:01.927544+00:00
-- url     : https://prove2.me/theorems/66653285-ce6b-4d35-9b32-1e3101e5b46a
-- title:
--   Equation (14), p. 8 — maximal time distortion occurs at a knot
-- statement:
--   Let $\chi_0=\theta_0=0$, with the inspection-grid times $\chi_\ell$ strictly increasing, and fix $m\ge1$. Let $\Delta$ be the interpolation between $(\chi_\ell,\theta_\ell)$ up to $m$, with slope one afterwards. Then the largest absolute time displacement is attained and equals the largest displacement at a knot:
--
--   $$
--   \sup_{s\ge0}|\Delta(s)-s|
--     =\max_{1\le\ell\le m}|\theta_\ell-\chi_\ell|.
--   $$
--
--   This deterministic identity converts the grid discrepancy of Lemma 1 into the time-distortion term of the $J_1$ metric.
--
--   **Formalization Note** Lean states that the right side is the greatest member of the set of all time-displacement values, which includes both the supremum equality and attainment.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, p. 8, equation (14)

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

/-- Equation (14), p. 8: the largest time distortion occurs at a grid knot. -/
theorem eq_14 (χ θ : ℕ → ℝ) (m : ℕ)
    (hχ0 : χ 0 = 0) (hθ0 : θ 0 = 0)
    (hχ : StrictMono χ) (hm : 1 ≤ m) :
    IsGreatest
      ((fun t : ℝ => |timeChange χ θ m t - t|) '' Set.Ici (0 : ℝ))
      (maxGap θ χ m) := by sorry

end InhomMJPStrong.J1
