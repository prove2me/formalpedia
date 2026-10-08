-- Prove2me | Theorems.Thm_MechanismDesign_Robust_no_undominated_interim_pareto
-- name    : MechanismDesign.Robust.no_undominated_interim_pareto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:20:38.337977+00:00
-- url     : https://prove2.me/theorems/e2f54e25-9beb-4eec-8648-376d7f9bc0df
-- title:
--   Proposition 10.10 -- no undominated auction for interim Pareto welfare on the space of finite types
-- statement:
--   In the single unit auction problem with $N \ge 3$ buyers whose values lie in $[\underline\theta,\overline\theta]$, $0 \le \underline\theta < \overline\theta$, suppose the designer's objective is interim Pareto welfare and the type space is the space $\mathcal T^+$ of all finite types. Then the set of undominated mechanisms is empty: for every mechanism $M$ with a Bayesian equilibrium $\sigma$ on $\mathcal T^+$ there are a mechanism $M'$ and a Bayesian equilibrium $\sigma'$ on $\mathcal T^+$ such that every type's interim expected utility is at least as large under $(M',\sigma')$ as under $(M,\sigma)$, and at some type profile some type's is strictly larger.
--
--   Because agents with inconsistent beliefs are willing to take arbitrarily large bets, a designer who respects agents' interim evaluations can always improve.
--
--   **Formalization Note** Mechanisms have arbitrary strategy sets; outcomes are an allocation and a vector of transfers, with lotteries over them.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.194, Proposition 10.10

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Auction

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.10 (Börgers p.194). In the single unit auction problem with `N ≥ 3` buyers
(values `θ_i ∈ [θ̲, θ̄]`, `0 ≤ θ̲ < θ̄`, utilities `θ_i − t_i` or `−t_i`), on the space `T⁺` of all
finite types and with interim Pareto welfare as the designer's objective, the set of undominated
mechanisms is empty: every mechanism with a Bayesian equilibrium on `T⁺` is dominated (Definition
10.16) by some mechanism with a Bayesian equilibrium on `T⁺`. -/
theorem no_undominated_interim_pareto {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 3 ≤ Fintype.card ι) (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    [∀ i, Nonempty (AuctionValue ι lo hi i)]
    (S : ι → Type) (M : Mechanism S (AuctionOutcome ι))
    (σ : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S i))
    (hσ : IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M σ) :
    ∃ (S' : ι → Type) (M' : Mechanism S' (AuctionOutcome ι))
      (σ' : ∀ i, TPlusType (AuctionValue ι lo hi) i → PMF (S' i)),
      IsBayesEq (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M' σ' ∧
      Dominates (interimWelfare (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M' σ')
        (interimWelfare (TPlus (AuctionValue ι lo hi)) (auctionUtility lo hi) M σ) := by sorry

end MechanismDesign.Robust
