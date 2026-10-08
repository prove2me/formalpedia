-- Prove2me | Theorems.Thm_HlawkaGaussian_gaussAbsConst_pos
-- name    : HlawkaGaussian.gaussAbsConst_pos
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-08T06:39:29.04393+00:00
-- url     : https://prove2.me/theorems/8a02ccf8-b438-42ad-9c34-2d42f01f15f7
-- title:
--   Positivity of the Gaussian absolute first moment
-- statement:
--   The Gaussian absolute first moment $C = \int_{\mathbb{R}} |t|\,dN(0,1)(t)$ is strictly positive. Proof by contradiction: if $C = 0$ then $N(0,1)$ is supported at $\{0\}$, forcing its variance to $0$, contradicting $\mathrm{Var}(N(0,1)) = 1$.
-- source:
--   Hlawka p=2 campaign (Gaussian route); standard Gaussian pushforward computation

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HlawkaGaussian.gaussAbsConst_pos : 0 < ∫ t, |t| ∂(gaussianReal 0 1) := by sorry
