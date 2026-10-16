-- Prove2me | Theorems.Thm_OAI_Thorp_Young_partition_count_le_sqrt_pow
-- name    : OAI.Thorp.Young.partition_count_le_sqrt_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:32:03.007951+00:00
-- url     : https://prove2.me/theorems/092c81ee-a27e-4090-b526-f01545919ccd
-- title:
--   The partition bound $p(n)\le(n+1)^{2\lfloor\sqrt n\rfloor}$
-- statement:
--   For a natural number $n$, let $p(n)$ be the number of partitions of $n$, i.e. of finite multisets of positive integers with sum $n$ (so $p(0)=1$). Then for every $n\ge 0$,
--
--   $$
--   p(n)\le(n+1)^{2\lfloor\sqrt{n}\rfloor}.
--   $$
--
--   Equivalently $\log p(n)\le 2\sqrt{n}\,\log(n+1)$, so the number of partitions grows subexponentially. This crude but explicit bound suffices whenever a sum over the partitions of $n$, such as a sum over the irreducible representations of the symmetric group $S_n$, has terms that decay exponentially in $n$: the number of terms is then negligible.
--
--   **Formalization Note** $p(n)$ is `Fintype.card (Nat.Partition n)` and $\lfloor\sqrt n\rfloor$ is the integer square root `Nat.sqrt n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/PartitionBounds.lean#L136-L170

import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds

open OAI OAI.Thorp OAI.Thorp.Young
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical

theorem OAI.Thorp.Young.partition_count_le_sqrt_pow (n : ℕ) :
    Fintype.card (Nat.Partition n) ≤ (n + 1) ^ (2 * Nat.sqrt n) := by sorry
