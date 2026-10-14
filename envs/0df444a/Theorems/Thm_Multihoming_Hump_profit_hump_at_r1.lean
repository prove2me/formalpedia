-- Prove2me | Theorems.Thm_Multihoming_Hump_profit_hump_at_r1
-- name    : Multihoming.Hump.profit_hump_at_r1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:40.090584+00:00
-- url     : https://prove2.me/theorems/fa497d2c-0c7c-4b48-aad0-6dfe1a54a514
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — πᴹ is hump-shaped in μ on [0, t] with peak at r₁
-- statement:
--   Let $t>0$ and $0\le e<2t$, and let $\pi^M(\mu)=t(t-\mu)(e+\mu)^2/((t+\mu)(2t-\mu)^2)$ be the symmetric profit (26). Then the root $r_1$ of Appendix A1 lies in the open interval $(0,t)$, and
--   $$\pi^M \text{ is strictly increasing on } [0,r_1] \quad\text{and strictly decreasing on } [r_1,t].$$
--
--   This is the profit half of Proposition 3, with the peak identified: the profit-maximizing network-effect strength is $r_1$.
--
--   **Formalization Note** The domain is the closed interval $\mu\in[0,t]$, as in the paper's proof; Assumption 1(i) is $\mu<t$, and since $\pi^M$ is continuous at $t$ the statement on $[0,t)$ is equivalent. The hypothesis $0\le e<2t$ is the condition the proof uses ("a necessary condition for partial multihoming").
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, sentence "Since there is only one value of μ for which dπᴹ/dμ = 0 …"

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 28: πᴹ is hump-shaped in μ on [0, t], with its peak at r₁ ∈ (0, t):
strictly increasing on [0, r₁] and strictly decreasing on [r₁, t]. -/
theorem profit_hump_at_r1 (t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    r1 t e ∈ Set.Ioo 0 t ∧
    StrictMonoOn (fun μ => piM t μ e) (Set.Icc 0 (r1 t e)) ∧
    StrictAntiOn (fun μ => piM t μ e) (Set.Icc (r1 t e) t) := by sorry

end Multihoming.Hump
