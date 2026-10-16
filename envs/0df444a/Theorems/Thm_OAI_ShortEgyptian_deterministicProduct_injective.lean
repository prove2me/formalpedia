-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_deterministicProduct_injective
-- name    : OAI.ShortEgyptian.deterministicProduct_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:20:43.501012+00:00
-- url     : https://prove2.me/theorems/06666dcd-bc7d-4756-bd94-63f0cdc17081
-- title:
--   Distinct subsets of distinct primes have distinct products
-- statement:
--   Let $J$ be a finite set and $p\colon J\to\mathbb{N}$, $j\mapsto p_j$, an injective map whose values are all prime. For a Boolean vector $I\in\{0,1\}^J$ put
--
--   $$\Pi_p(I)=\prod_{j\in J}\begin{cases}p_j,&I_j=1,\\ 1,&I_j=0,\end{cases}\qquad\text{that is,}\qquad \Pi_p(I)=\prod_{j:\ I_j=1}p_j .$$
--
--   Then the map $I\mapsto\Pi_p(I)$ from $\{0,1\}^J$ to $\mathbb{N}$ is injective:
--
--   $$
--   \Pi_p(I)=\Pi_p(K)\ \Longrightarrow\ I=K\qquad\bigl(I,K\in\{0,1\}^J\bigr).
--   $$
--
--   This is unique factorization in the special form needed for squarefree products: the $2^{|J|}$ subset products of $|J|$ distinct primes are pairwise distinct. It guarantees that the deterministic list of subset products has $2^{|J|}$ distinct entries, which is the hypothesis needed to apply the mean-square equidistribution bound for injective lists.
--
--   **Formalization Note** $\{0,1\}^J$ is `J → Bool` and $\Pi_p$ is `deterministicProduct p`, defined as `∏ j, if I j then p j else 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean#L21-L39

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction

open OAI OAI.ShortEgyptian
universe uJ uA uR
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.deterministicProduct_injective {J : Type uJ} [Fintype J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    Function.Injective (deterministicProduct p) := by sorry
