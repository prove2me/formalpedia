-- Prove2me | Theorems.Thm_KellyReversibility_PartialBalance_partial_balance_equivalences
-- name    : KellyReversibility.PartialBalance.partial_balance_equivalences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:01:38.993362+00:00
-- url     : https://prove2.me/theorems/3d80c83d-0292-461e-abc9-6e320c044b6e
-- title:
--   Theorem 9.5 — partial balance ⇔ truncation keeps the conditional law ⇔ rate changes inside or across $\mathcal A$ ⇔ reversal and truncation commute ⇔ exit and entry chains agree
-- statement:
--   Let a Markov process on a finite state space $\mathcal S$ have transition rates $q(j,k)$ ($q(j,k)\ge0$ for $j\ne k$, $q(j,j)=0$), be irreducible, and have equilibrium distribution $\pi(j)$, $j\in\mathcal S$ (positive, summing to one, satisfying the equilibrium equations). Let $\mathcal A\subseteq\mathcal S$ be nonempty, with the process truncated to $\mathcal A$ irreducible within $\mathcal A$, and let $c>0$, $c\ne1$. The following statements are equivalent.
--
--   1. $\pi$ satisfies the partial balance conditions
--   $$\pi(j)\sum_{k\in\mathcal A}q(j,k)=\sum_{k\in\mathcal A}\pi(k)q(k,j),\qquad j\in\mathcal A.$$
--   2. If the process is truncated to $\mathcal A$, the equilibrium distribution of the truncated process is the conditional distribution $\pi(j)/\sum_{k\in\mathcal A}\pi(k)$, $j\in\mathcal A$.
--   3. If $q(j,k)$ is changed to $c\,q(j,k)$ for $j,k\in\mathcal A$, the resulting process has the unaltered equilibrium distribution $\pi$.
--   4. If $q(j,k)$ is changed to $c\,q(j,k)$ for $j\in\mathcal A$, $k\in\mathcal S-\mathcal A$, the equilibrium distribution of the resulting process is $B\pi(j)$ for $j\in\mathcal A$ and $Bc\pi(j)$ for $j\in\mathcal S-\mathcal A$, where $B^{-1}=\sum_{j\in\mathcal A}\pi(j)+c\sum_{j\in\mathcal S-\mathcal A}\pi(j)$.
--   5. Time reversal and truncation to $\mathcal A$ commute: if $p$ is the equilibrium distribution of the truncated process, then
--   $$\frac{p(k)q(k,j)}{p(j)}=\frac{\pi(k)q(k,j)}{\pi(j)},\qquad j,k\in\mathcal A.$$
--
--   If moreover $\mathcal S-\mathcal A$ is nonempty, these are also equivalent to:
--
--   6. The Markov chain formed by observing the process at the instants just before it leaves $\mathcal A$ has the same equilibrium distribution as the Markov chain formed by observing it at the instants just after it enters $\mathcal A$.
--
--   Theorem 9.5 gathers Exercises 1.6.2–1.6.4 and 1.7.7–1.7.8 of the book; partial balance is the hypothesis under which several properties of reversible processes survive without detailed balance.
--
--   **Formalization Note** The state space is finite, so the book's additional condition for (vi), finiteness of the flux $\sum_{j\in\mathcal A}\sum_{k\in\mathcal S-\mathcal A}\pi(j)q(j,k)$, holds automatically. "The equilibrium distribution of a process is $X$" means $X$ is positive, sums to one, satisfies the equilibrium equations, and is the only such distribution. The book's "$c\ne0$ or $1$" is read as $c>0$, $c\ne1$, so altered rates stay non-negative; for such $c$ the altered processes are irreducible because $q$ is. The embedded exit and entry chains are defined through jump-chain path sums in `ExitEntryChains`; their equilibrium distributions are non-negative and vanish on states from which no exit, resp. into which no entry, occurs.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 200–201, Theorem 9.5

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_ExitEntryChains

namespace KellyReversibility.PartialBalance

open KellyStochasticNetworks

/-- **Theorem 9.5** (Kelly 1979, pp. 200–201). For an irreducible Markov process on a finite
state space with rates `q` and equilibrium distribution `π`, a nonempty set `A` within which the
truncated process is irreducible, and a constant `c > 0`, `c ≠ 1`, statements (i)–(v) are
equivalent; when `S − A` is nonempty they are also equivalent to (vi). -/
theorem partial_balance_equivalences {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) (hAirr : IsIrreducible (truncatedRates q A))
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≠ 1) :
    List.TFAE
      [ IsPartialBalance π q A,
        IsTheEquilibriumDist (truncatedRates q A) (condDist π A),
        IsTheEquilibriumDist (scaleWithin q A c) π,
        IsTheEquilibriumDist (scaleExit q A c) (exitScaledDist π A c),
        ∀ p : A → ℝ, IsTheEquilibriumDist (truncatedRates q A) p →
          reversedRates p (truncatedRates q A) = truncatedRates (reversedRates π q) A ] ∧
    (Aᶜ.Nonempty →
      (IsPartialBalance π q A ↔
        ∃ μ : A → ℝ, IsTheStationaryDist (exitChain q A) μ ∧
          IsTheStationaryDist (entryChain q A) μ)) := by sorry

end KellyReversibility.PartialBalance
