-- Prove2me | Theorems.Thm_Multihoming_Local_closed_forms
-- name    : Multihoming.Local.closed_forms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:40.895354+00:00
-- url     : https://prove2.me/theorems/5c46a0ba-6ec8-4762-9cbc-88f247c5456e
-- title:
--   (19)–(20), PDF p. 18 (printed p. 12) — closed forms of s_i, m and x_i at the candidate prices
-- statement:
--   Let $t>0$ and $0\le\mu<t$, and evaluate the multihoming demand (14) at the candidate prices (16). Then the number of singlehomers of good $i$, the number of multihomers and the output of good $i$ are
--
--   $$
--   s_i=\frac{(2t^2-\mu^2)\big((t-\mu)(\mu+2t)-e_jt\big)+e_i\mu t^2}{\mu^4-5\mu^2t^2+4t^4}, \qquad (19)
--   $$
--
--   $$
--   m=\frac{(e_0+e_1)t+\mu^2-2t^2+\mu t}{(2t-\mu)(\mu+t)}, \qquad
--   x_i=\frac{\mu(2t+\mu)(t-\mu)+(2t^2-\mu^2)e_i-t\mu e_j}{(t^2-\mu^2)(4t^2-\mu^2)}\,t. \qquad (20)
--   $$
--
--   In the statement $(e_0,e_1)$ in the formula for $m$ is $(e_i,e_j)$; $m$ is symmetric in the two goods. These closed forms make the dependence on $\mu$ explicit and underlie the comparative statics (22).
--
--   **Formalization Note** The factor $t$ at the end of (20) multiplies the whole fraction, as on the page.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 18 (printed p. 12), (19), (20)

import Mathlib
import Definitions.Def_Multihoming_Local_Model

namespace Multihoming.Local

/-- (19)–(20), PDF p. 18: closed forms of the singlehomers `s_i`, the multihomers `m` and the
output `x_i` at the candidate prices (16). -/
theorem closed_forms (t μ ei ej : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    singleM t μ ei ej =
        ((2 * t ^ 2 - μ ^ 2) * ((t - μ) * (μ + 2 * t) - ej * t) + ei * μ * t ^ 2) /
          (μ ^ 4 - 5 * μ ^ 2 * t ^ 2 + 4 * t ^ 4) ∧
      multiM t μ ei ej = ((ei + ej) * t + μ ^ 2 - 2 * t ^ 2 + μ * t) / ((2 * t - μ) * (μ + t)) ∧
      outM t μ ei ej =
        (μ * (2 * t + μ) * (t - μ) + (2 * t ^ 2 - μ ^ 2) * ei - t * μ * ej) /
          ((t ^ 2 - μ ^ 2) * (4 * t ^ 2 - μ ^ 2)) * t := by sorry

end Multihoming.Local
