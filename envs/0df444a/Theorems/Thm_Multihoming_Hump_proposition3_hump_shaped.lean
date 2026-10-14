-- Prove2me | Theorems.Thm_Multihoming_Hump_proposition3_hump_shaped
-- name    : Multihoming.Hump.proposition3_hump_shaped
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:41.333029+00:00
-- url     : https://prove2.me/theorems/6d0992d7-09d8-4b38-a15a-d25c9cd10c7b
-- title:
--   Proposition 3, PDF p. 20 (printed p. 14) — under partial multihoming, price and profit are hump-shaped in μ
-- statement:
--   **Proposition 3.** Assume partial multihoming. Prices and profits are then hump-shaped functions of the strength of network effects.
--
--   Precisely: let $t>0$ be the mismatch cost and let both goods have $e$ exclusive features with $0\le e<2t$. Consider the symmetric multihoming price and profit (26) as functions of the network-effect strength $\mu\in[0,t]$,
--   $$p^M(\mu)=\frac{(t-\mu)(\mu+e)}{2t-\mu},\qquad \pi^M(\mu)=\frac{t\,(t-\mu)\,(e+\mu)^2}{(t+\mu)\,(2t-\mu)^2}.$$
--   Then
--
--   1. there is $\hat\mu_p\in(0,t)$ such that $p^M$ is strictly increasing on $[0,\hat\mu_p]$ and strictly decreasing on $[\hat\mu_p,t]$;
--   2. there is $\hat\mu_\pi\in(0,t)$ such that $\pi^M$ is strictly increasing on $[0,\hat\mu_\pi]$ and strictly decreasing on $[\hat\mu_\pi,t]$.
--
--   Network effects therefore benefit the firms when they are weak and harm them when they are strong; as $\mu\to t$ the goods become as if undifferentiated and the price falls to $0$.
--
--   **Formalization Note** "Assume partial multihoming" is pinned as $0\le e<2t$: the paper's proof uses exactly $2t-e>0$, "a necessary condition for partial multihoming", and $e\ge0$ counts exclusive features. For $e\in(t,2t)$ the partial-multihoming range $e\le\bar e(\mu)=(2t^2-\mu^2)/t$ fails for $\mu$ near $t$, and for $e<t$ the range $e\ge\underline e(\mu)=(t-\mu)(2t+\mu)/(2t)$ fails for $\mu$ near $0$; like the paper's proof, the statement is about the closed forms (26) on all of $[0,t]$. The interval is closed at $t$, as in the proof, which evaluates at $\mu=t$; Assumption 1(i) is $\mu<t$, and since both functions are continuous at $t$ the statement on $[0,t)$ is equivalent. The peaks lie in the open interval $(0,t)$, so neither function is monotone on $[0,t]$. The profit is the closed form (26); on $[0,t)$ it equals price times the demand (14), which is a separate theorem of this mission.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 20 (printed p. 14), Proposition 3; proof Appendix A1, PDF pp. 28–29 (printed pp. 22–23)

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Proposition 3, PDF p. 20: under partial multihoming (pinned as 0 ≤ e < 2t), the symmetric
price pᴹ and profit πᴹ of (26) are hump-shaped in μ on [0, t]: each strictly increases up to an
interior peak and strictly decreases after it. -/
theorem proposition3_hump_shaped (t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    (∃ μp ∈ Set.Ioo 0 t,
        StrictMonoOn (fun μ => Multihoming.Thresholds.pM t μ e) (Set.Icc 0 μp) ∧
        StrictAntiOn (fun μ => Multihoming.Thresholds.pM t μ e) (Set.Icc μp t)) ∧
    (∃ μπ ∈ Set.Ioo 0 t,
        StrictMonoOn (fun μ => piM t μ e) (Set.Icc 0 μπ) ∧
        StrictAntiOn (fun μ => piM t μ e) (Set.Icc μπ t)) := by sorry

end Multihoming.Hump
