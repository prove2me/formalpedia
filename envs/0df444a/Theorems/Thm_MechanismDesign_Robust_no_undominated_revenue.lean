-- Prove2me | Theorems.Thm_MechanismDesign_Robust_no_undominated_revenue
-- name    : MechanismDesign.Robust.no_undominated_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:21:02.675173+00:00
-- url     : https://prove2.me/theorems/1adf9290-e6f9-4a3f-b965-04af7daf9cc1
-- title:
--   Proposition 10.11 -- no undominated auction for ex post revenue on the space of finite types
-- statement:
--   In the single unit auction problem with $N \ge 3$ buyers whose values lie in $[\underline\theta,\overline\theta]$, $0 \le \underline\theta < \overline\theta$, suppose the designer's objective is ex post revenue and the type space is the space $\mathcal T^+$ of all finite types. Then the set of undominated mechanisms is empty: for every mechanism $M$ with a Bayesian equilibrium $\sigma$ on $\mathcal T^+$ there are a mechanism $M'$ and a Bayesian equilibrium $\sigma'$ on $\mathcal T^+$ whose expected revenue $\mathbb E\sum_i t_i$ is at least as large at every type profile and strictly larger at some.
--
--   A revenue-maximizing designer can charge fees for arranging bets between agents with inconsistent beliefs.
--
--   **Formalization Note** Revenue at a type profile is the expected sum of transfers under the equilibrium lottery; its existence (absolute summability) at every type profile is required of the mechanisms compared, as the welfare function of Definition 10.14 takes real values.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.194, Proposition 10.11

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Auction

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.11 (Börgers p.194). In the single unit auction problem with `N ≥ 3` buyers, on
the space `T⁺` of all finite types and with ex post revenue as the designer's objective, the set
of undominated mechanisms is empty: every mechanism with a Bayesian equilibrium on `T⁺` whose
expected revenue exists at every type profile is dominated by some such mechanism. -/
theorem no_undominated_revenue {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 3 ≤ Fintype.card ι) (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    [∀ i, Nonempty (AuctionValue ι lo hi i)]
    (S : ι → Type) (M : Mechanism S (AuctionOutcome ι))
    (σ : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S i))
    (hσ : IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M σ)
    (hrev : ∀ τ, Summable fun x => (eqOutcome M σ τ x).toReal * ∑ i, x.2 i) :
    ∃ (S' : ι → Type) (M' : Mechanism S' (AuctionOutcome ι))
      (σ' : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S' i)),
      IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M' σ' ∧
      (∀ τ, Summable fun x => (eqOutcome M' σ' τ x).toReal * ∑ i, x.2 i) ∧
      Dominates (revenueWelfare M' σ') (revenueWelfare M σ) := by sorry

end MechanismDesign.Robust
