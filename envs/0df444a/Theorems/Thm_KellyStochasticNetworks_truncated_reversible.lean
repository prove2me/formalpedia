-- Prove2me | Theorems.Thm_KellyStochasticNetworks_truncated_reversible
-- name    : KellyStochasticNetworks.truncated_reversible
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:42:10.316933+00:00
-- url     : https://prove2.me/theorems/82777b21-b704-43ea-b51f-c9834cb5fbd3
-- title:
--   Lemma 3.4 — truncating a reversible process
-- statement:
--   Let $q$ be the transition rates of a Markov process on a state space $S$, and let
--   $\pi = (\pi(j))_{j \in S}$ be in detailed balance with $q$, so that the process is
--   **reversible** with equilibrium distribution $\pi$. **Truncate** the process to a subset
--   $A \subseteq S$: keep the rates between states of $A$ unchanged and suppress every transition
--   that would leave $A$.
--
--   Then the truncated process is again reversible, with equilibrium distribution
--   $$\pi(j)\Bigl(\sum_{k \in A}\pi(k)\Bigr)^{-1}, \qquad j \in A .$$
--   Precisely, if the sum $Z = \sum_{k \in A}\pi(k)$ converges and is non-zero, then
--   $j \mapsto \pi(j)/Z$ is in detailed balance with the truncated rates and its terms sum to $1$.
--
--   This is the lever of the whole chapter. A loss network is the truncation of a system of
--   independent, uncapacitated queues to the feasible set $\{n : An \le C\}$, and because the
--   uncapacitated system is reversible the lemma hands over its equilibrium distribution at once:
--   independent Poisson random variables conditioned on a set of linear inequalities.
--
--   **Formalization Note** The truncated process lives on the subtype of states belonging to $A$,
--   so the suppression of transitions leaving $A$ is automatic: such a transition has no target.
--   Convergence of $Z$ and its value are asserted together.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 53 (PDF p. 61), Lemma 3.4: 'If a reversible Markov process with state space S and equilibrium distribution (pi(j), j in S) is truncated to A subset of S, the resulting Markov process is reversible and has equilibrium distribution pi(j) (sum_{k in A} pi(k))^{-1}, j in A. (3.2)' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks

theorem truncated_reversible {S : Type*} (π : S → ℝ) (q : S → S → ℝ) (A : Set S)
    (h : DetailedBalance π q) (Z : ℝ) (hZ0 : Z ≠ 0)
    (hZ : HasSum (fun j : A => π (j : S)) Z) :
    DetailedBalance (fun j : A => π (j : S) / Z) (truncatedRates q A)
      ∧ HasSum (fun j : A => π (j : S) / Z) 1 := by sorry

end KellyStochasticNetworks
