-- Prove2me | Theorems.Thm_MarkovDecisionProcesses_average_optimality_bounds
-- name    : MarkovDecisionProcesses.average_optimality_bounds
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:26:21.208831+00:00
-- url     : https://prove2.me/theorems/bd9cef12-d260-44d3-9c2c-10ec510b314e
-- title:
--   Theorem 8.4.1 — sub- and supersolutions of the optimality equation bound the optimal gain
-- statement:
--   Consider a stationary MDP with finite state and action sets, a scalar $g$ and a function
--   $h:S\to\mathbb R$, and let $B(g,h)(s)=\max_{a\in A_s}\{r(s,a)-g+\sum_jp(j\mid s,a)h(j)-h(s)\}$.
--
--   - (a) If $B(g,h)\le 0$ at every state, then $g\ge g^*_+(s)$ for every $s$: no policy has
--     lim sup average reward above $g$.
--   - (b) If $B(g,h)\ge 0$ at every state, then for every $s$,
--     $g\le\sup_{d\in D^{MD}}g^{d^\infty}_-(s)\le g^*_-(s)$: some deterministic stationary policy
--     has lim inf average reward at least $g$.
--   - (c) If $B(g,h)=0$ at every state, then $g^*_+(s)=g$ and $g^*_-(s)=g$ for every $s$.
--
--   This is Theorem 8.4.1, the average reward analogue of Theorem 6.2.2 (mission II) and, in the
--   source's words, "one of the most important results for average reward models; part (c) gives
--   the main result". Part (a) follows by iterating the inequality $ge\ge r_d+(P_d-I)h$ along any
--   policy and averaging, the telescoping term $(P^\pi_N-I)h$ vanishing after division by $N$;
--   part (b) uses the decision rule attaining the maximum; (c) is (a) and (b) together.
--
--   **Formalization Note** The source states the theorem for countable $S$; the model of this
--   mission is finite, as the chapter's Assumption 8.0.3, so the statement is the finite case. In
--   (b) the source writes $g^{d^\infty}$, the gain of a stationary policy, which exists as a limit
--   on a finite chain; it is formalized as the lim inf gain, which equals it. In (c) the source's
--   chain $ge=g^*=g^*_+=g^*_-$ is stated through its two computable members $g^*_+$ and $g^*_-$,
--   since $g^*$ is defined only where the limits exist. The suprema over policies and over
--   deterministic decision rules are real suprema of nonempty families bounded by $\max|r|$.
-- source:
--   Martin L. Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley 1994, https://doi.org/10.1002/9780470316887 — §8.4.1, printed p. 356 (PDF p. 372), Theorem 8.4.1: "Suppose S is countable. a. If there exists a scalar g and an h ∈ V which satisfy B(g, h) ≤ 0, then ge ≥ g*_+. (8.4.4) b. If there exists a scalar g and h ∈ V which satisfy B(g, h) ≥ 0, then ge ≤ sup_{d∈D^MD} g^{d^∞} ≤ g*_−. (8.4.5) c. If there exists a scalar g and an h ∈ V for which B(g, h) = 0, then ge = g* = g*_+ = g*_−. (8.4.6)"

import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace MarkovDecisionProcesses
theorem average_optimality_bounds {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (g : ℝ) (h : S → ℝ) :
    ((∀ s, optimalityResidual M g h s ≤ 0) → ∀ s, optGainSup M s ≤ g) ∧
    ((∀ s, 0 ≤ optimalityResidual M g h s) →
      ∀ s, g ≤ (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
                  gainInf (stationaryPolicy M d.1 d.2) s) ∧
        (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
            gainInf (stationaryPolicy M d.1 d.2) s) ≤ optGainInf M s) ∧
    ((∀ s, optimalityResidual M g h s = 0) →
      ∀ s, optGainSup M s = g ∧ optGainInf M s = g) := by sorry
end MarkovDecisionProcesses
