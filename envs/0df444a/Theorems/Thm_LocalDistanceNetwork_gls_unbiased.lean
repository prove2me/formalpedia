-- Prove2me | Theorems.Thm_LocalDistanceNetwork_gls_unbiased
-- name    : LocalDistanceNetwork.gls_unbiased
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:24:34.454302+00:00
-- url     : https://prove2.me/theorems/d64f4349-d3dc-46e1-8907-04ca6f602cc7
-- title:
--   GLS estimator is linear and unbiased: $(A^{\mathsf T}WA)^{-1}A^{\mathsf T}W\,A=I$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank and let $W\in\mathbb R^{m\times m}$ be symmetric positive definite. Then the GLS estimator matrix $L_W=(A^{\mathsf T}WA)^{-1}A^{\mathsf T}W$ is a left inverse of $A$:
--   $$
--   L_W\,A=I_n .
--   $$
--
--   Consequently, if the data satisfy $Y=AX_0+\varepsilon$ with $\mathbb E[\varepsilon]=0$, then $\mathbb E[L_WY]=X_0$: the GLS estimator is a linear unbiased estimator, one half of the "Best Linear Unbiased Estimator" property invoked in Appendix B.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace LocalDistanceNetwork
theorem gls_unbiased {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (W : Matrix m m ℝ) (hW : W.PosDef) :
    glsEstimatorMatrix A W * A = 1 := by sorry
end LocalDistanceNetwork
