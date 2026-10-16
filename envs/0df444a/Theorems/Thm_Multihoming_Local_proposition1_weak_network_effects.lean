-- Prove2me | Theorems.Thm_Multihoming_Local_proposition1_weak_network_effects
-- name    : Multihoming.Local.proposition1_weak_network_effects
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:29.419423+00:00
-- url     : https://prove2.me/theorems/e7083034-2a71-48d5-ad36-7ee980cab611
-- title:
--   Proposition 1, PDF p. 19 (printed p. 13) — near μ = 0, network effects raise each firm's demand, price and profit and lower its singlehomers
-- statement:
--   Consider the Hotelling duopoly with network effects of strength $\mu$, mismatch cost $t>0$ and exclusive features $e_0,e_1$ of the two goods, at the candidate partial-multihoming prices $p_i^M$ of (16). Write $x_i(\mu)$ for the total demand of good $i$ (the multihoming demand (14) at those prices), $s_i(\mu)=1-x_j(\mu)$ for its singlehomers, and $\pi_i(\mu)=p_i^M(\mu)\,x_i(\mu)$ for firm $i$'s profit.
--
--   Assume partial multihoming at $\mu=0$, that is
--
--   $$
--   e_0<2t,\qquad e_1<2t,\qquad 2t<e_0+e_1 .
--   $$
--
--   Then there is $\delta$ with $0<\delta<t$ such that, on $[0,\delta]$ and for each $i\in\{0,1\}$,
--
--   1. the total demand $x_i(\mu)$ is strictly increasing in $\mu$;
--   2. the number of singlehomers $s_i(\mu)$ is strictly decreasing in $\mu$;
--   3. the price $p_i^M(\mu)$ is strictly increasing in $\mu$;
--   4. the profit $\pi_i(\mu)$ is strictly increasing in $\mu$.
--
--   The firms may be asymmetric ($e_0\ne e_1$). In contrast with full singlehoming, where prices and profits strictly fall in $\mu$, weak network effects benefit both firms once some consumers multihome.
--
--   **Formalization Note** "Assume partial multihoming" is pinned as the three inequalities above: at $\mu=0$ the closed forms (19)–(20) give $s_0=(2t-e_1)/(2t)$, $s_1=(2t-e_0)/(2t)$ and $m=(e_0+e_1-2t)/(2t)$, so these are exactly the conditions under which both groups of singlehomers and the multihomers are positive. (The page names only one condition $2t-e_i>0$; both firms' conditions are needed.) "In the neighborhood of $\mu=0$" is read as strict monotonicity on $[0,\delta]$ for some $\delta>0$; it is one-sided because $\mu\ge0$, and $\delta<t$ keeps Assumption 1 (i), $\mu<t$. Assumption 1 (ii)–(iii) (coverage and positive shares in the full game) are not used and not assumed. Demand is the multihoming demand (14) at the candidate prices (16), not a closed form.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 19 (printed p. 13), Proposition 1; argument PDF pp. 18–19, (21), (22), footnote 15

import Mathlib
import Definitions.Def_Multihoming_Local_Model

namespace Multihoming.Local

/-- Proposition 1, PDF p. 19: under partial multihoming at `μ = 0` (`e₀, e₁ < 2t < e₀ + e₁`),
there is `δ ∈ (0, t)` such that on `[0, δ]` each good's total demand, price and profit at the
candidate prices (16) strictly increase in `μ`, and each good's singlehomers strictly decrease. -/
theorem proposition1_weak_network_effects (t e0 e1 : ℝ) (ht : 0 < t)
    (h0 : e0 < 2 * t) (h1 : e1 < 2 * t) (hpm : 2 * t < e0 + e1) :
    ∃ δ, 0 < δ ∧ δ < t ∧
      (StrictMonoOn (fun μ => outM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => outM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictAntiOn (fun μ => singleM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictAntiOn (fun μ => singleM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictMonoOn (fun μ => priceM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => priceM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictMonoOn (fun μ => profitM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => profitM t μ e1 e0) (Set.Icc 0 δ)) := by sorry

end Multihoming.Local
