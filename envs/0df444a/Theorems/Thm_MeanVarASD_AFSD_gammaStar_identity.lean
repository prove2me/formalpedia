-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_gammaStar_identity
-- name    : MeanVarASD.AFSD.gammaStar_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:35.502178+00:00
-- url     : https://prove2.me/theorems/fb026cf9-a4c9-45ff-9332-2b3d018def57
-- title:
--   Proof of Theorem 7, p. 8 — f(−t)/(2t + f(−t)) = (−t + √(1 + t²))/(t + √(1 + t²)) = 1/(1 + 2t(t + √(t² + 1)))
-- statement:
--   Let $f(z)=z+\sqrt{1+z^2}$. For every real $t$,
--   $$\frac{f(-t)}{2t+f(-t)}=\frac{-t+\sqrt{1+t^2}}{t+\sqrt{1+t^2}}=\frac{1}{1+2t\big(t+\sqrt{t^2+1}\big)}=\gamma^*(t).$$
--
--   This identifies the root $\gamma$ of the equation $\gamma t=(1-\gamma)\tfrac12 f(-t)$, which is where $A(\gamma,\delta^*)=B(\gamma,\delta^*)$, with the closed form of the threshold $\gamma^*$ stated in Theorem 7.
--
--   **Formalization Note** All denominators are positive for every real $t$ ($t+\sqrt{1+t^2}>0$), so no division by zero occurs.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 8 (PDF 9), proof of Theorem 7, last line of the computation of γ*

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

/-- Proof of Theorem 7, p. 8: `f(−t)/(2t + f(−t)) = (−t + √(1 + t²))/(t + √(1 + t²))
= 1/(1 + 2t(t + √(t² + 1)))` for every real `t`. -/
theorem gammaStar_identity (t : ℝ) :
    fAux (-t) / (2 * t + fAux (-t)) = (-t + Real.sqrt (1 + t ^ 2)) / (t + Real.sqrt (1 + t ^ 2)) ∧
      (-t + Real.sqrt (1 + t ^ 2)) / (t + Real.sqrt (1 + t ^ 2)) = gammaStar t := by sorry

end MeanVarASD.AFSD
