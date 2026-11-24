-- Prove2me | Theorems.Thm_FractionalCalc_laplace_mittagLefflerOne
-- name    : FractionalCalc.laplace_mittagLefflerOne
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T16:42:26.210998+00:00
-- url     : https://prove2.me/theorems/341b04df-9a7d-42db-96d9-34bbe194370e
-- title:
--   Laplace transform of $E_\alpha(-\lambda t^\alpha)$ (Eq. 25)
-- statement:
--   For $\alpha>0$ and $\lambda\in\mathbb R$, and $\operatorname{Re}s>|\lambda|^{1/\alpha}$,
--   $$\mathcal L\big[E_\alpha(-\lambda t^\alpha)\big](s)=\frac{s^{\alpha-1}}{s^\alpha+\lambda}=\frac{s^{-1}}{1+\lambda s^{-\alpha}}.$$
--   This is Eq. (25) of the source, the $\beta=1$ case of Eq. (26); it generalizes $\mathcal L[e^{-\lambda t}]=1/(s+\lambda)$.
--
--   **Formalization Note** The printed first fraction in Eq. (25) reads $s^{\alpha-1}/(s^\alpha+1)$, a typo: the paper's own second expression $s^{-1}/(1+\lambda s^{-\alpha})$ and Eq. (26) at $\beta=1$ give the denominator $s^\alpha+\lambda$, which is formalized here. The Lean binder `c` stands for $\lambda$.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §4, Eq. (25). Printed denominator $s^\alpha+1$ corrected to $s^\alpha+\lambda$ (consistent with the same equation's second form and Eq. (26), $\beta=1$).

import Mathlib
import Definitions.Def_FractionalCalc_mittagLeffler
import Definitions.Def_QueueingFundamentals_Transient_laplace
open MeasureTheory Set Classical QueueingFundamentals.Transient

namespace FractionalCalc
theorem laplace_mittagLefflerOne (α c : ℝ) (s : ℂ)
    (hα : 0 < α) (hs : |c| ^ (1 / α) < s.re) :
    laplace (fun t => mittagLefflerOne α (-c * t ^ α)) s =
      s ^ (α - 1 : ℂ) / (s ^ (α : ℂ) + c) := by sorry
end FractionalCalc
