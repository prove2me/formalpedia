-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_prescribed_function_card_le
-- name    : OAI.ThorpCompatibility.prescribed_function_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:47:57.672969+00:00
-- url     : https://prove2.me/theorems/fc79715e-cc83-4e9c-a35a-96532e800ca4
-- title:
--   At most $(N-|s|)!$ permutations agree with a prescribed map on $s$
-- statement:
--   Let $\alpha$ be a finite set with $|\alpha|=N$, let $s\subseteq\alpha$, and let $f:\alpha\to\alpha$ be an arbitrary map. Then the number of permutations of $\alpha$ that agree with $f$ on $s$ satisfies
--
--   $$
--   \#\{\tau\in\mathrm{Sym}(\alpha):\ \tau(x)=f(x)\ \text{for all }x\in s\}\;\le\;(N-|s|)!\,.
--   $$
--
--   Prescribing the values of a permutation on $s$ leaves at most $(N-|s|)!$ possibilities, whether or not the prescription is injective. This is convenient for bounding joint probabilities such as $\Pr[\tau(k)=t,\ \tau(l)=u]\le\frac{(N-2)!}{N!}$ for a uniformly random permutation $\tau$ and $k\ne l$, without first checking that the prescribed values are distinct.
--
--   **Formalization Note** $N-|s|$ is natural-number subtraction, which is never truncated since $|s|\le N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/PermutationCount.lean#L35-L54

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.prescribed_function_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card ≤
      (Fintype.card α - s.card).factorial := by sorry
