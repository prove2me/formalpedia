-- Prove2me | Theorems.Thm_FreeOrderEPTAS_delta_calibration
-- name    : FreeOrderEPTAS.delta_calibration
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:58.246592+00:00
-- url     : https://prove2.me/theorems/b387e067-87a5-4baf-a7fd-a9de5aab824f
-- title:
--   §2.5, inequality (9): the explicit $\delta$ is calibrated
-- statement:
--   Let $\epsilon\in(0,1)$ and let $\delta=2^{-r}$ with $r=(8(mD+1)(\lceil1/\epsilon\rceil+1))^2$. For any Santa Claus instance, with $T$ the number of classes induced by $(\epsilon,\delta)$ and $mDT\ge1$,
--   $$\delta\le\frac{\epsilon^3}{16\,T\ln(2mDT)}.$$
--
--   This is the calibration that makes the union bound of Lemma 2.3 close: the number of classes grows only polylogarithmically in $1/\delta$.
--
--   Differences from the source:
--   - reading: $\delta=(\epsilon^3/(32mD\psi^{2/3}))^3$, assuming $1/\delta$ is an integer, for a constant $\psi$ not specified → explicit $\delta=2^{-r}$ with $r=(8(mD+1)(\lceil1/\epsilon\rceil+1))^2$; reason: the source only requires (9) and an integer $1/\delta$, depending on $(\epsilon,m,D)$; the explicit value has both
--   - encoding: (9), used for a small triple $(i,d,t)$, with $\epsilon\in(0,1)$ → hypotheses $mDT\ge1$ and $\epsilon\in(0,1)$; reason: at $mDT=0$ the right side divides by $\ln 0$, a junk value $0$, and no triple exists; "small constants $\delta,\epsilon\in(0,1)$", p.9
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.5, p.12; inequality (9), pp.15–16

import Mathlib
import Definitions.Def_FreeOrderEPTAS_typeList
import Definitions.Def_FreeOrderEPTAS_delta

namespace FreeOrderEPTAS

/-- §2.5, p.12 and the end of the proof of Claim 2.4, pp.15–16 (arXiv:2007.13121v3): the explicit
`δ = 2^{-r}` satisfies inequality (9), `δ ≤ ϵ³ / (16 T ln(2mDT))`, for the number `T` of classes it
induces. -/
theorem delta_calibration {m D n : ℕ} (I : SCInstance m D n) (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hpos : 0 < m * D * numTypes I ϵ (delta ϵ m D)) :
    delta ϵ m D ≤ ϵ ^ 3 / (16 * (numTypes I ϵ (delta ϵ m D) : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ (delta ϵ m D) : ℝ))) := by sorry

end FreeOrderEPTAS
