-- Prove2me | Theorems.Thm_OptimisticPSRL_Diameter_exists_policy_attaining_minTravel
-- name    : OptimisticPSRL.Diameter.exists_policy_attaining_minTravel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:39.054396+00:00
-- url     : https://prove2.me/theorems/af64c5f7-aabd-41fc-a01d-ad5a5bac9b09
-- title:
--   Proof of Lemma 5.6, p. 13 — in a communicating MDP one deterministic policy attains the minimum expected time to a target from every state
-- statement:
--   Let $\mathcal M$ be a finite MDP with $S$ states and $A\ge 1$ actions whose diameter $D(\mathcal M)$ is finite (that is, $\mathcal M$ is communicating, Definition 3). Fix a target state $s_2$ and let $E^{s_2}_{s'}=\min_{\pi} T^{\pi}_{s'\to s_2}$ be the minimum, over deterministic stationary policies $\pi:\mathcal S\to\mathcal A$, of the expected number of steps to reach $s_2$ from $s'$.
--
--   Then there is a single deterministic stationary policy $\pi$ that attains all of these minima at once:
--   $$T^{\pi}_{s'\to s_2} = E^{s_2}_{s'}\qquad\text{for every } s'\in\mathcal S.$$
--
--   In the proof of Lemma 5.6 the authors take a policy $\pi$ that reaches $s_2$ from $s_1$ within $D$ expected steps and then identify the vector of its expected times from every state with the sub-vector of $E^{s_2}$; this identification is the statement above. It is the existence of a uniformly optimal stationary deterministic policy for the minimum-expected-hitting-time (stochastic shortest path) problem.
--
--   **Formalization Note.** States and actions are `Fin S`, `Fin A` (0-based). $T^{\pi}_{s'\to s_2}$ is the platform's `mdpTravelTime M f s' s₂` (the expected hitting time minus one, in $[0,\infty]$), and $E^{s_2}$ is `minTravel M s₂`. Two hypotheses are pinned relative to the page: `mdpDiameterENN M ≠ ⊤`, the paper's standing assumption that $\mathcal M$ has (finite) diameter $D$; and `0 < A`, the paper's nonempty action set, needed because with $S=1$, $A=0$ the diameter is the empty supremum $0$ but no policy exists.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 13, proof of Lemma 5.6, first paragraph (E is the sub-vector of E^{s_2})

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_OptimisticPSRL_Diameter_Setting
open BanditAlgorithm NNReal ENNReal

namespace OptimisticPSRL.Diameter
theorem exists_policy_attaining_minTravel {S A : ℕ} (M : FiniteMDP S A)
    (hD : mdpDiameterENN M ≠ ⊤) (hA : 0 < A) (tgt : Fin S) :
    ∃ f : Fin S → Fin A, ∀ src : Fin S, mdpTravelTime M f src tgt = minTravel M tgt src := by sorry
end OptimisticPSRL.Diameter
