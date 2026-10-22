-- Prove2me | Theorems.Thm_MallowsChoice_DP_lemma_1
-- name    : MallowsChoice.DP.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:19.048158+00:00
-- url     : https://prove2.me/theorems/41a6de73-df8a-47dd-9a0a-4faa588674f4
-- title:
--   Lemma 1, p. 17 — repeated insertion samples the Mallows distribution
-- statement:
--   Fix a concentration parameter $\theta\ge0$. For every $m\ge0$, run Algorithm 1 on the first $m$ products, taking $a_1\cdots a_m$ as the modal ranking. For every ranking $\tau$ of those products, the probability that repeated insertion returns $\tau$ equals its Mallows probability:
--
--   $$
--   \Pr\{\operatorname{RIM}_m=\tau\}
--     =\frac{\exp(-\theta d(\tau,a_1\cdots a_m))}{\psi_m(\theta)}.
--   $$
--
--   This identifies the sampler used in the dynamic-program derivation with the distribution used to define choice probabilities.
--
--   **Formalization Note** The paper states the result for Algorithm 1 on $n$ products; it applies equally to each prefix $m$, whose insertion probabilities do not depend on the final $n$. At $m=0$ both sides assign mass one to the unique empty ranking.
-- source:
--   Désir, Goyal, Jagabathula & Segev, Mallows-Smoothed Distribution over Rankings Approach for Modeling Choice, SSRN 3172997 (manuscript OPRE-2018-04-176, version of 2019-09-25; Oper. Res. doi:10.1287/opre.2020.2085), Lemma 1 (citing Lu and Boutilier 2014, Theorem 3), p. 17

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

namespace MallowsChoice.DP

/-- Lemma 1 (Lu and Boutilier 2014, Theorem 3), p. 17. -/
theorem lemma_1 (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ (m : ℕ) (τ : Equiv.Perm (Fin m)), rimProb θ m τ = mallows θ τ := by sorry

end MallowsChoice.DP
