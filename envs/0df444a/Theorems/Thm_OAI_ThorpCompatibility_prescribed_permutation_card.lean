-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_prescribed_permutation_card
-- name    : OAI.ThorpCompatibility.prescribed_permutation_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:47:31.513975+00:00
-- url     : https://prove2.me/theorems/8b403025-f805-49cc-8437-dee8ca02328a
-- title:
--   Number of permutations agreeing with a given permutation on a subset
-- statement:
--   Let $\alpha$ be a finite set with $|\alpha|=N$, let $s\subseteq\alpha$, and let $\sigma$ be a permutation of $\alpha$. Then the number of permutations of $\alpha$ that agree with $\sigma$ on $s$ is
--
--   $$
--   \#\{\tau\in\mathrm{Sym}(\alpha):\ \tau(x)=\sigma(x)\ \text{for all }x\in s\}\;=\;(N-|s|)!\,.
--   $$
--
--   Equivalently, a uniformly random permutation of $\alpha$ agrees with $\sigma$ on $s$ with probability $(N-|s|)!/N!$. This exact count is the basic input for computing probabilities of rank events, such as $\{\tau(k)=t\}$, for a uniformly random permutation.
--
--   **Formalization Note** The subset $s$ is a `Finset α`, and $N-|s|$ is natural-number subtraction, which is never truncated since $|s|\le N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/PermutationCount.lean#L8-L33

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.prescribed_permutation_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (σ : Equiv.Perm α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x)).card =
      (Fintype.card α - s.card).factorial := by sorry
