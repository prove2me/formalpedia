-- Prove2me | Theorems.Thm_GenEllipPot_Potential_lemma_2_2_potential
-- name    : GenEllipPot.Potential.lemma_2_2_potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:53.400643+00:00
-- url     : https://prove2.me/theorems/bc006535-929c-41bf-8937-3a1de166e38c
-- title:
--   Lemma 2.2(3), p. 4: potential inequality (2.2)
-- statement:
--   For a positive semidefinite matrix $\Sigma$, $x>0$, and any $V\in\mathbb R^d$, define
--
--   $$\Sigma'=\Sigma-\frac{\Sigma VV^\top\Sigma}{1+V^\top\Sigma V}.$$
--
--   Then
--
--   $$\log(1+V^\top\Sigma V)+f(\Sigma',x)\le f(\Sigma,x+V^\top V),\qquad f(S,z)=\log\det(I+zS).$$
--
--   This compares one quadratic-form increment and the residual covariance potential with the potential at a larger scalar argument.
--
--   **Formalization Note.** The second, square-root factorization of $\Sigma'$ printed after (2.2) is an equivalent expression and is represented by the displayed first formula.
-- source:
--   Hamidi & Bayati, The Elliptical Potential Lemma for General Distributions with an Application to Linear Thompson Sampling, arXiv:2102.07987v3, p. 4, Lemma 2.2 item 3, equation (2.2); proof p. 9

import Mathlib
import Definitions.Def_GenEllipPot_Potential_Model

open Matrix

namespace GenEllipPot.Potential

/-- Lemma 2.2(3), the matrix potential inequality (2.2), p. 4. -/
theorem lemma_2_2_potential (d : ℕ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (x : ℝ) (hx : 0 < x) (V : Fin d → ℝ) :
    let S' := S - (1 + V ⬝ᵥ (S *ᵥ V))⁻¹ •
      (S * Matrix.vecMulVec V V * S)
    Real.log (1 + V ⬝ᵥ (S *ᵥ V)) + potF S' x ≤
      potF S (x + V ⬝ᵥ V) := by sorry

end GenEllipPot.Potential
