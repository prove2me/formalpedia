-- Prove2me | Theorems.Thm_MaxEntOCRS_closing_step
-- name    : MaxEntOCRS.closing_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:45.481434+00:00
-- url     : https://prove2.me/theorems/384fe00c-cadd-4470-b81a-c8449affc1ab
-- title:
--   Proof of Theorem 2, closing step — (4) and (5) force $t \le t^* = (2-\sqrt3)/3$
-- statement:
--   Let $r, t$ be real numbers with $r < 1/2$ and $t < 1$ such that
--   $$
--   2r(1 - r) \le \alpha(1 - t) \quad \text{(Eq. (4) with } \kappa = 1 - t\text{)}, \qquad t \le r(\alpha + \beta t) \quad \text{(Eq. (5))}.
--   $$
--   Then
--   $$
--   t \le t^* = \frac{2 - \sqrt3}{3} .
--   $$
--   In the proof of Theorem 2, $K > C$ forces $t > t^*$, so this step yields the contradiction that proves $K \le C$. The bound is attained at the four-cycle, where $r = \alpha/\sqrt3$ and $t = t^*$.
--
--   Differences from the source:
--   - generalization: r, t the normalized quantities of the proof of Theorem 2 (with r < 1/3 and t < 1 from the Normalization paragraph) → all real r < 1/2 and t < 1 satisfying (4) with κ = 1 − t and (5); reason: the step uses only these inequalities; the paper's r, t satisfy them
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 6, Closing the argument, p.8 (A.7 Closing, p.15)

import Mathlib
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_beta

namespace MaxEntOCRS

/-- The closing step of the proof of Theorem 2 (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §6, p.8; A.7 "Closing", p.15): if
`r < 1/2`, `t < 1`, `2r(1 − r) ≤ α(1 − t)` (Eq. (4) with `κ = 1 − t`) and `t ≤ r(α + βt)`
(Eq. (5)), then `t ≤ t* = (2 − √3)/3` ("(4) yields r ≤ ρ(t), (5) gives Ψ(t) ≥ 0, …
Therefore t ≤ t*"). -/
theorem closing_step (r tN : ℝ) (hr : r < 1 / 2) (htN : tN < 1)
    (h4 : 2 * r * (1 - r) ≤ alpha * (1 - tN)) (h5 : tN ≤ r * (alpha + beta * tN)) :
    tN ≤ (2 - Real.sqrt 3) / 3 := by sorry

end MaxEntOCRS
