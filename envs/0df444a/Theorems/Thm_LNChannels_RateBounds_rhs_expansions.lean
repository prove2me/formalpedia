-- Prove2me | Theorems.Thm_LNChannels_RateBounds_rhs_expansions
-- name    : LNChannels.RateBounds.rhs_expansions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:53.394129+00:00
-- url     : https://prove2.me/theorems/50859adf-cfc3-4447-85ff-fd0be767a18a
-- title:
--   Eqs. (5)–(6), pp. 6–7 — the thresholds are $Br/\lambda+o(r)$ and $3(Br^2/(4\lambda^2))^{1/3}-Br/(12\lambda)+o(r)$ as $r\to0$
-- statement:
--   Fix $B>0$ and $\lambda>0$ and let the discount rate $r$ tend to $0$ from above. Then
--   $$\log\Big(1+B\log\big(1+\tfrac r\lambda\big)\Big)=\frac{Br}{\lambda}+o(r),$$
--   and, with $\kappa(r)=\log\dfrac{r+2\lambda+\sqrt{r(4\lambda+r)}}{2\lambda}$,
--   $$3\Big(\frac{B\kappa(r)^4}{4}\Big)^{1/3}-\frac B{12}\kappa(r)^2=3\Big(\frac{Br^2}{4\lambda^2}\Big)^{1/3}-\frac{Br}{12\lambda}+o(r).$$
--
--   These are the small-rate readings of the thresholds in Theorem 2: the unidirectional threshold is linear in $r$, the symmetric bidirectional one of order $r^{2/3}$.
--
--   **Formalization Note** Each $o(r)$ is Mathlib's little-o (`IsLittleO`) along $r\to0^+$ (the filter `𝓝[>] 0`) with $B$ and $\lambda$ fixed; the difference of the two sides is $o(r)$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, pp. 6–7 (PDF pp. 7–8), Theorem 2, right-hand sides of eqs. (5) and (6)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

open Asymptotics Filter Topology

namespace LNChannels.RateBounds

/-- The right-hand expansions in (5) and (6), pp. 6–7: for fixed `B, λ > 0`, as `r → 0⁺`,
`log(1 + B log(1 + r/λ)) = Br/λ + o(r)` and, with `κ(r) = log((r + 2λ + √(r(4λ + r)))/(2λ))`,
`3(Bκ⁴/4)^{1/3} − (B/12)κ² = 3(Br²/(4λ²))^{1/3} − Br/(12λ) + o(r)`. -/
theorem rhs_expansions (lam B : ℝ) (hlam : 0 < lam) (hB : 0 < B) :
    (fun r : ℝ => Real.log (1 + B * Real.log (1 + r / lam)) - B * r / lam) =o[𝓝[>] 0]
        (fun r : ℝ => r) ∧
      (fun r : ℝ =>
          let κ := Real.log ((r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam));
          (3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2)
            - (3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) - B * r / (12 * lam))) =o[𝓝[>] 0]
        (fun r : ℝ => r) := by sorry

end LNChannels.RateBounds
