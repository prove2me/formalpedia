-- Prove2me | Theorems.Thm_FractionalCalc_laplace_prabhakar_of_le_two
-- name    : FractionalCalc.laplace_prabhakar_of_le_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T15:48:45.473032+00:00
-- url     : https://prove2.me/theorems/33c287ae-648b-422a-ab57-a27e8a050dd3
-- title:
--   Laplace transform of $t^{\beta-1}E_{\alpha,\beta}^\gamma(-\lambda t^\alpha)$ (Eq. 27), for $\alpha\le 2$
-- statement:
--   For $0<\alpha\le2$, $\beta>0$, $\gamma\in\mathbb R$ and $\lambda\in\mathbb R$, and $\operatorname{Re}s>|\lambda|^{1/\alpha}$,
--   $$\mathcal L\big[t^{\beta-1}E_{\alpha,\beta}^{\gamma}(-\lambda t^\alpha)\big](s)=\frac{s^{\alpha\gamma-\beta}}{(s^\alpha+\lambda)^\gamma}.$$
--   This is Eq. (27) of the source, the transform of the three-parameter (Prabhakar) Mittag-Leffler function, generalizing Eq. (26) (the case $\gamma=1$).
--
--   **Formalization Note** The Lean binder `c` stands for $\lambda$. Complex powers are principal values. The restriction $\alpha\le2$ keeps $\alpha\arg s$ inside $(-\pi,\pi)$ on the half plane, so that the principal value of $(s^\alpha+\lambda)^\gamma$ equals $s^{\alpha\gamma}(1+\lambda s^{-\alpha})^\gamma$; for larger $\alpha$ and non-integer $\gamma$ the right hand side as written can differ from the transform by a root of unity.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §4, Eq. (27).

import Mathlib
import Definitions.Def_FractionalCalc_mittagLeffler
import Definitions.Def_QueueingFundamentals_Transient_laplace
open MeasureTheory Set Classical QueueingFundamentals.Transient

namespace FractionalCalc
theorem laplace_prabhakar_of_le_two (α β γ c : ℝ) (s : ℂ)
    (hα : 0 < α) (hα2 : α ≤ 2) (hβ : 0 < β) (hs : |c| ^ (1 / α) < s.re) :
    laplace (fun t => t ^ (β - 1) * prabhakar α β γ (-c * t ^ α)) s =
      s ^ (α * γ - β : ℂ) / (s ^ (α : ℂ) + c) ^ (γ : ℂ) := by sorry
end FractionalCalc
