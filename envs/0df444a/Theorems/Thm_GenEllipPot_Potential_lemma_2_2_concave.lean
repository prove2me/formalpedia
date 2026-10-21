-- Prove2me | Theorems.Thm_GenEllipPot_Potential_lemma_2_2_concave
-- name    : GenEllipPot.Potential.lemma_2_2_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:06.512207+00:00
-- url     : https://prove2.me/theorems/0e77588d-8f11-4459-b3c7-553830187bdf
-- title:
--   Lemma 2.2(1), p. 4: concavity of log det(I+xΣ)
-- statement:
--   Fix $x>0$ and let $f(\Sigma,x)=\log\det(I+x\Sigma)$ for a positive semidefinite real matrix $\Sigma$. Then $f(\cdot,x)$ is concave on the positive semidefinite cone:
--
--   $$f(\lambda\Sigma_1+(1-\lambda)\Sigma_2,x)\ge\lambda f(\Sigma_1,x)+(1-\lambda)f(\Sigma_2,x)\quad(0\le\lambda\le1).$$
--
--   This is the matrix concavity used when conditioning the next posterior covariance in Theorem 2.1.
-- source:
--   Hamidi & Bayati, The Elliptical Potential Lemma for General Distributions with an Application to Linear Thompson Sampling, arXiv:2102.07987v3, p. 4, Lemma 2.2 item 1; proof p. 9

import Mathlib
import Definitions.Def_GenEllipPot_Potential_Model

namespace GenEllipPot.Potential

/-- Lemma 2.2(1), concavity of the log-determinant potential, p. 4. -/
theorem lemma_2_2_concave (d : ℕ) (x : ℝ) (hx : 0 < x) :
    ConcaveOn ℝ {S : Matrix (Fin d) (Fin d) ℝ | S.PosSemidef}
      (fun S => potF S x) := by sorry

end GenEllipPot.Potential
