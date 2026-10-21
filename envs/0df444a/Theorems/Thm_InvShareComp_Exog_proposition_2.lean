-- Prove2me | Theorems.Thm_InvShareComp_Exog_proposition_2
-- name    : InvShareComp.Exog.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:08.493803+00:00
-- url     : https://prove2.me/theorems/50080628-7b26-41c1-9973-d6a3b4db4a83
-- title:
--   Proposition 2, p. 17 (PDF 17), corrected — t̂* = c̄ − δ is optimal, sharing at it is preferred, and for β > 0 no transfer price coordinates
-- statement:
--   Under the standing assumptions, let the demand factors have an exchangeable law on $[0,1]^2$ with a density, let the exogenous inventories be $I_1=I_2=I\in[0,1]$, and suppose
--   $$p\mu-A-B>0\quad\text{at } t=\bar c-\delta ,$$
--   i.e. $\hat s(\bar c-\delta,I)>0$ when $\beta>0$. Then:
--
--   1. **Optimal transfer price.** For every $t\in[0,\bar c-\delta]$, every symmetric sharing equilibrium $(s,s)$ at $t$ and every symmetric sharing equilibrium $(s',s')$ at $\hat t^*=\bar c-\delta$, each retailer's profit at $(s,s)$ is at most its profit at $(s',s')$.
--   2. **Sharing is preferred.** For every symmetric sharing equilibrium $(s',s')$ at $\hat t^*$ and every symmetric no-sharing equilibrium $(s^N,s^N)$, each retailer's no-sharing profit is at most its sharing profit.
--   3. **No coordination.** If $\beta>0$, then for every $t\in[0,\bar c-\delta]$ and every symmetric sharing equilibrium $(s,s)$ at $t$, each retailer earns strictly less than the centralized half-profit $\pi^c(I,I)/2$ of (A.1), and $s\neq0=s^c$.
--
--   The highest non-moot transfer price is thus optimal for both retailers and makes sharing worthwhile, but under service competition no transfer price restores the centralized outcome.
--
--   **Formalization Note.** *Corrected.* The guard $p\mu-A-B>0$ at $\bar c-\delta$ replaces the proof's unproved "$\hat s(t,I)>0$ for any $t$ given that $\beta>0$"; without it the proposition fails (i.i.d. bimodal demand, density $\propto e^{-(x-0.05)^2/0.002}+e^{-(x-0.95)^2/0.002}$, $p=1$, $\bar c=0.9$, $\delta=0$, $c=0.3$, $I=0.324$, $\beta=0.1$, $k=1$: the profit at the closed-form level peaks near $t\approx0.605$, where it equals $\pi^c(I,I)/2$). "The optimal transfer price is $\bar c-\delta$" is read as "$\bar c-\delta$ is a maximizer": at $I=0$ no sharing happens and every $t$ is optimal. "Prefer" is weak ($\le$), following tie-break rule (1) on p. 10. Statements quantify over equilibria; existence for $\beta>0$ is not asserted (Lemma 3(a)'s existence half is not established in general). Deviations keep both deterministic demands non-negative; the bound $\beta\le\bar\beta$ of (A.7) is not assumed.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), p. 17 (PDF 17), Proposition 2; proof in Online Appendix p. 10 (PDF 42)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem proposition_2 (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (hS0 : 0 < SVal P ν (P.cbar - P.δ) I) :
    (∀ t ∈ Set.Icc 0 (P.cbar - P.δ), ∀ s s' : ℝ,
        IsSymEqShare P ν t I s → IsSymEqShare P ν (P.cbar - P.δ) I s' →
        profitShare1 P ν t I I s s ≤ profitShare1 P ν (P.cbar - P.δ) I I s' s' ∧
        profitShare2 P ν t I I s s ≤ profitShare2 P ν (P.cbar - P.δ) I I s' s') ∧
    (∀ s' sN : ℝ, IsSymEqShare P ν (P.cbar - P.δ) I s' → IsSymEqNoShare P ν I sN →
        profitNo1 P ν I I sN sN ≤ profitShare1 P ν (P.cbar - P.δ) I I s' s' ∧
        profitNo2 P ν I I sN sN ≤ profitShare2 P ν (P.cbar - P.δ) I I s' s') ∧
    (0 < P.β → ∀ t ∈ Set.Icc 0 (P.cbar - P.δ), ∀ s : ℝ, IsSymEqShare P ν t I s →
        profitShare1 P ν t I I s s < centralProfit P ν I I / 2 ∧
        profitShare2 P ν t I I s s < centralProfit P ν I I / 2 ∧ s ≠ 0) := by sorry

end InvShareComp.Exog
