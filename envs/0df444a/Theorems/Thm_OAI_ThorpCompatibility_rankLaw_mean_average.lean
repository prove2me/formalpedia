-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_rankLaw_mean_average
-- name    : OAI.ThorpCompatibility.rankLaw_mean_average
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:50:25.513166+00:00
-- url     : https://prove2.me/theorems/b344bc4a-b067-44dc-811f-c173235abc0b
-- title:
--   Averaging rank-conditioned permutation laws over the rank recovers the uniform law
-- statement:
--   Let $D\ge1$, let $S_D$ be the group of permutations of $[D]=\{0,1,\dots,D-1\}$, and fix $k\in[D]$. For $t\in[D]$ let $\rho_{k,t}$ be the uniform distribution on $S_D$ conditioned on the event $\{e(k)=t\}$, i.e. the uniform distribution on the $(D-1)!$ permutations $e$ with $e(k)=t$. Then for every function $g:S_D\to\mathbb{R}$,
--
--   $$
--   \frac1D\sum_{t\in[D]}\mathbb E_{e\sim\rho_{k,t}}\big[g(e)\big]\;=\;\mathbb E_{e\sim\mathrm{Unif}(S_D)}\big[g(e)\big].
--   $$
--
--   This is the law of total expectation for the decomposition of a uniformly random permutation according to the rank $e(k)$ of a fixed element, whose law is uniform on $[D]$. It allows bounds proved separately for each rank-conditioned law $\rho_{k,t}$ to be averaged into a bound for the uniform law.
--
--   **Formalization Note** $\rho_{k,t}$ is `rankLaw k t`, defined as the restriction of `Law.uniform` to $\{e(k)=t\}$; since this event has probability $1/D>0$, the restriction is a genuine conditional law. The existence of an element $k$ of `Fin D` forces $D\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/RankAverages.lean#L62-L77

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.rankLaw_mean_average {D : ℕ} (k : Fin D) (g : Equiv.Perm (Fin D) → ℝ) :
    (∑ t, (rankLaw k t).mean g) / (D : ℝ) =
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean g := by sorry
