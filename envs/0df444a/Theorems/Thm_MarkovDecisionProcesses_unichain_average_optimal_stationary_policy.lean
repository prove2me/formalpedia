-- Prove2me | Theorems.Thm_MarkovDecisionProcesses_unichain_average_optimal_stationary_policy
-- name    : MarkovDecisionProcesses.unichain_average_optimal_stationary_policy
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:29:03.258362+00:00
-- url     : https://prove2.me/theorems/016fcb2c-dc6c-4433-8ff2-53cf06595765
-- title:
--   Theorem 8.4.5 — existence of average optimal stationary policies in finite unichain models
-- statement:
--   Consider a stationary MDP with finite state and action sets that is unichain. Then
--
--   - (a) there is a deterministic stationary policy $d^\infty$ that is **average optimal**:
--     $g^{d^\infty}_-(s)\ge g^\pi_+(s)$ for every state $s$ and every $\pi\in\Pi^{HR}$;
--   - (b) there are a scalar $g^*$ and a function $h^*:S\to\mathbb R$ with $B(g^*,h^*)=0$, and
--     (d) this $g^*$ is the optimal gain under both remaining criteria: $g^*_+(s)=g^*_-(s)=g^*$
--     for every $s$;
--   - (c) for every solution $(g^*,h^*)$ of the optimality equation and every $h^*$-improving
--     decision rule $d$, the stationary policy $d^\infty$ is average optimal.
--
--   This is Theorem 8.4.5, the chapter's existence theorem for unichain models, which the source
--   assembles from Theorem 8.4.3 (existence of a solution), Theorem 8.4.4 (an improving rule is
--   optimal) and Theorem 8.4.1 (the solution's scalar is the optimal gain). It is what justifies
--   solving the single optimality equation $B(g,h)=0$ — by policy iteration, value iteration or
--   linear programming in Sections 8.5 to 8.8 — instead of searching over policies, and it is why
--   the three average optimality criteria of Section 8.1.2 coincide in finite unichain models.
--
--   **Formalization Note** Bounded rewards are automatic in a finite model. Part (d) is stated
--   together with (b), as the identity $g^*_+=g^*_-=g^*$ for the scalar of the solution exhibited
--   there; by Theorem 8.4.3(b) that scalar is the same for every solution. Part (a) exhibits a
--   deterministic stationary policy, which is what "stationary" means in the chapter's Section
--   8.3.1 classification and is what the proof produces. "Average optimal" is criterion (8.1.7),
--   the strongest of the three, against every history-dependent randomized policy.
-- source:
--   Martin L. Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley 1994, https://doi.org/10.1002/9780470316887 — §8.4.3, printed p. 361 (PDF p. 377), Theorem 8.4.5: "Suppose S is finite and A_s is finite for each s ∈ S, r(s, a) is bounded and the model is unichain. Then a. there exists a stationary average optimal policy, b. there exists a scalar g* and an h* ∈ V for which B(g*, h*) = 0, c. any stationary policy derived from an h*-improving decision rule is average optimal, and d. g*e = g*_+ = g*_−."

import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace MarkovDecisionProcesses
theorem unichain_average_optimal_stationary_policy {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M) :
    (∃ (d : S → A) (hd : ∀ s, d s ∈ M.admissible s),
        IsAverageOptimal (stationaryPolicy M d hd)) ∧
    (∃ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) ∧
        ∀ s, optGainSup M s = gstar ∧ optGainInf M s = gstar) ∧
    (∀ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) →
        ∀ (d : S → A) (hd : IsImproving M hstar d),
          IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1))) := by sorry
end MarkovDecisionProcesses
