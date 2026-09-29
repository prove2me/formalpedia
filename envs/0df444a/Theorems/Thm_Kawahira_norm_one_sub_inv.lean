-- Prove2me | Theorems.Thm_Kawahira_norm_one_sub_inv
-- name    : Kawahira.norm_one_sub_inv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:05:14.469494+00:00
-- url     : https://prove2.me/theorems/2008df3c-2fbd-4392-a733-b64026a1dca7
-- title:
--   Norm classification for a reciprocal translation
-- statement:
--   For a nonzero complex number $w$, the multiplier $1-w^{-1}$ lies on the unit circle exactly when $\operatorname{Re}(w)=1/2$, and it lies strictly inside the unit disk exactly when $\operatorname{Re}(w)>1/2$. This elementary geometric criterion is reusable when classifying fixed points of Newton-type maps.
-- source:
--   Elementary complex norm identity; used in T. Kawahira, The Riemann Hypothesis and Holomorphic Index in Complex Dynamics, Experimental Mathematics (2016), Propositions 5, 7–9, https://doi.org/10.1080/10586458.2016.1217443.

import Mathlib

open Complex

namespace Kawahira

theorem norm_one_sub_inv (w : ℂ) (hw : w ≠ 0) :
    (‖1 - w⁻¹‖ = 1 ↔ w.re = 1 / 2) ∧
      (‖1 - w⁻¹‖ < 1 ↔ 1 / 2 < w.re) := by sorry
