-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_uniform_rank_prob
-- name    : OAI.ThorpCompatibility.uniform_rank_prob
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:49:53.084147+00:00
-- url     : https://prove2.me/theorems/da094aec-fd8a-4d17-8497-f30fa436d216
-- title:
--   A uniformly random permutation sends $k$ to $t$ with probability $1/D$
-- statement:
--   Let $D$ be a positive integer, let $S_D$ be the group of permutations of $[D]=\{0,1,\dots,D-1\}$, and let $e$ be a uniformly random element of $S_D$. For all $k,t\in[D]$,
--
--   $$
--   \Pr_{e\sim\mathrm{Unif}(S_D)}\big[e(k)=t\big]\;=\;\frac1D .
--   $$
--
--   Viewing $e$ as a uniformly random ordering of $D$ items in which item $k$ receives rank $e(k)$, the rank of any fixed item is uniformly distributed on $[D]$. In particular every event $\{e(k)=t\}$ has positive probability, so the uniform law conditioned on it is a genuine conditional law, and averages over the rank $e(k)$ are plain averages over $t\in[D]$.
--
--   **Formalization Note** The existence of $k,t\in[D]$ (elements of `Fin D`) forces $D\ge1$. The uniform law on $S_D$ is `Law.uniform`, with mass $1/D!$ at every permutation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/RankLaw.lean#L37-L51

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

theorem OAI.ThorpCompatibility.uniform_rank_prob {D : ℕ} (k t : Fin D) :
    (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) = 1 / (D : ℝ) := by sorry
