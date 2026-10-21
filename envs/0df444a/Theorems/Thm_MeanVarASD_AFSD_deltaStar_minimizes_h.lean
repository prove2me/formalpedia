-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_deltaStar_minimizes_h
-- name    : MeanVarASD.AFSD.deltaStar_minimizes_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:38.145156+00:00
-- url     : https://prove2.me/theorems/eefe5650-bdd1-4ff7-95d4-04380d870194
-- title:
--   Proof of Theorem 7, p. 8 — for σX, σY > 0, δ* is the unique minimizer of h(δ) = σY f((δ − µY)/σY) + σX f((µX − δ)/σX)
-- statement:
--   Let $\sigma_X,\sigma_Y>0$, $\mu_X,\mu_Y\in\mathbb R$, $f(z)=z+\sqrt{1+z^2}$ and
--   $$h(\delta)=\sigma_Y f\Big(\frac{\delta-\mu_Y}{\sigma_Y}\Big)+\sigma_X f\Big(\frac{\mu_X-\delta}{\sigma_X}\Big),\qquad \delta^*=\frac{\mu_X\sigma_Y+\mu_Y\sigma_X}{\sigma_Y+\sigma_X}.$$
--   Then $h(\delta^*)\le h(\delta)$ for every $\delta$, with equality only at $\delta=\delta^*$.
--
--   Since $A(\gamma,\delta)\ge B(\gamma,\delta)$ holds exactly when $\gamma$ is at least a quantity increasing in $h(\delta)$, this shows that $\delta^*$ is the choice of $\delta$ giving the smallest threshold $\gamma^*$ obtainable by this argument.
--
--   **Formalization Note** The positivity of both standard deviations is needed for $h$ to be defined; the paper uses it implicitly in dividing by $\sigma_X$ and $\sigma_Y$.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 8 (PDF 9), proof of Theorem 7, first-order condition h′(δ) = 0 and its unique solution δ*

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

/-- Proof of Theorem 7, p. 8: for `σX, σY > 0`, `δ*` is the unique minimizer of `h`. -/
theorem deltaStar_minimizes_h (μX μY σX σY : ℝ) (hσX : 0 < σX) (hσY : 0 < σY) :
    ∀ δ, hAux μX μY σX σY (deltaStar μX μY σX σY) ≤ hAux μX μY σX σY δ ∧
      (hAux μX μY σX σY δ = hAux μX μY σX σY (deltaStar μX μY σX σY) →
        δ = deltaStar μX μY σX σY) := by sorry

end MeanVarASD.AFSD
