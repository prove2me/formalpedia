-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_A_ge_B_at_deltaStar
-- name    : MeanVarASD.AFSD.A_ge_B_at_deltaStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:00.846065+00:00
-- url     : https://prove2.me/theorems/9fd3ca9f-0ecf-4901-a67d-f98df83c163c
-- title:
--   Proof of Theorem 7, p. 8 — A(γ,δ*) ≥ B(γ,δ*) for all γ ≥ γ*, δ* = (µXσY + µYσX)/(σY + σX)
-- statement:
--   Let $\mu_X<\mu_Y$ and $\sigma_X,\sigma_Y\ge0$ with $\sigma_X+\sigma_Y>0$, and put
--   $$t=\frac{\mu_Y-\mu_X}{\sigma_Y+\sigma_X},\qquad \delta^*=\frac{\mu_X\sigma_Y+\mu_Y\sigma_X}{\sigma_Y+\sigma_X}.$$
--   Then for every $\gamma\ge\gamma^*(t)=1/\big(1+2t(t+\sqrt{t^2+1})\big)$,
--   $$A(\gamma,\delta^*)\ge B(\gamma,\delta^*).$$
--
--   Combined with the bounds $\mathbb E\,u_U(X;\delta)\le B(\gamma,\delta)$ and $\mathbb E\,u_L(Y;\delta)\ge A(\gamma,\delta)$ and the sandwich $u_L\le u\le u_U$, this is the inequality from which Theorem 7 follows.
--
--   **Formalization Note** The means and standard deviations are free reals here. The paper's $(\delta^*-\mu_Y)/\sigma_Y=(\mu_X-\delta^*)/\sigma_X=-t$ needs $\sigma_X,\sigma_Y>0$; the statement uses the square-root forms of $A$ and $B$, which are defined for $\sigma_X=0$ or $\sigma_Y=0$ as well, and only requires $\sigma_X+\sigma_Y>0$. No upper bound on $\gamma$ is needed.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 8 (PDF 9), proof of Theorem 7, δ* and the final sentence

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

/-- Proof of Theorem 7, p. 8: if `µX < µY`, `σX, σY ≥ 0`, `σX + σY > 0` and `γ ≥ γ*`, then
`A(γ, δ*) ≥ B(γ, δ*)`. -/
theorem A_ge_B_at_deltaStar (μX μY σX σY γ : ℝ) (hσX : 0 ≤ σX) (hσY : 0 ≤ σY)
    (hσ : 0 < σX + σY) (hμ : μX < μY) (hγ : gammaStar (tStat μX μY σX σY) ≤ γ) :
    Bval γ (deltaStar μX μY σX σY) μX σX ≤ Aval γ (deltaStar μX μY σX σY) μY σY := by sorry

end MeanVarASD.AFSD
