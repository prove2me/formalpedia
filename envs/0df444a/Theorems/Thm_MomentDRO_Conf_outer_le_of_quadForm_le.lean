-- Prove2me | Theorems.Thm_MomentDRO_Conf_outer_le_of_quadForm_le
-- name    : MomentDRO.Conf.outer_le_of_quadForm_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:06:47.814039+00:00
-- url     : https://prove2.me/theorems/324c4c9e-8d07-438a-8565-fad6eb7ce4bc
-- title:
--   Theorem 2 proof, p. 14 — rank-one covariance domination
-- statement:
--   Let $\Sigma$ be a positive definite covariance matrix and $d\in\mathbb R^m$. If $d^\mathsf T\Sigma^{-1}d\le b$, then
--   $$dd^\mathsf T\preceq b\Sigma.$$
--
--   In the proof of Theorem 2, $d=\widehat\mu-\mu$ and $b=\beta(\delta/2)$. This converts the mean-error bound into a matrix bound for the centring correction.
--
--   **Formalization Note** The matrix comparison is the Loewner order; positive definiteness ensures the inverse represents the intended quadratic form.
-- source:
--   Delage & Ye, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 14, §4.2, proof of Theorem 2, Cauchy–Schwarz display

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MomentDRO.Conf

theorem outer_le_of_quadForm_le {m : ℕ}
    (cov : Matrix (Fin m) (Fin m) ℝ) (hcov : cov.PosDef)
    (d : Fin m → ℝ) (b : ℝ)
    (hd : quadForm cov⁻¹ d ≤ b) :
    LoewnerLE (Matrix.vecMulVec d d) (b • cov) := by sorry

end MomentDRO.Conf
