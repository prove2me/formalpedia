-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_integer_rows_eventual_pair_rank
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.integer_rows_eventual_pair_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:25:16.380458+00:00
-- url     : https://prove2.me/theorems/7bc3cdfa-4a81-484c-b694-2e7a4724bcf2
-- title:
--   Pairwise non-proportional integer vectors stay pairwise independent modulo all large primes
-- statement:
--   Let $\iota$ and $J$ be finite index sets and let $a_j=(a_{jk})_{k\in\iota}\in\mathbb Z^{\iota}$, $j\in J$, be integer vectors. Assume
--
--   1. every $a_j$ is nonzero;
--   2. for all $j\ne l$ in $J$, the vector $a_l$ is not a rational multiple of $a_j$, that is, $a_l\ne c\,a_j$ for every $c\in\mathbb Q$.
--
--   Then there is a natural number $Q$ such that for every prime $q>Q$ and all $j\ne l$ in $J$ the linear map
--
--   $$
--   (\mathbb Z/q\mathbb Z)^{\iota}\longrightarrow(\mathbb Z/q\mathbb Z)^2,\qquad x\longmapsto\Big(\sum_{k\in\iota}a_{jk}x_k,\ \sum_{k\in\iota}a_{lk}x_k\Big)
--   $$
--
--   is surjective, where the integer coefficients $a_{jk}$ are reduced modulo $q$.
--
--   Equivalently, for all sufficiently large primes $q$ the reductions modulo $q$ of any two of the vectors are linearly independent over $\mathbb Z/q\mathbb Z$. Consequently, when $x$ is uniformly distributed on $(\mathbb Z/q\mathbb Z)^{\iota}$, any two of the forms $x\mapsto\sum_k a_{jk}x_k$ are jointly uniformly distributed on $(\mathbb Z/q\mathbb Z)^2$. In the Littlewood construction this is applied to the integer frequency rows of the signed interval-packing problem.
--
--   **Formalization Note** The linear forms are `dotForm (fun k => (a j k : ZMod q))`, and the pair map is their product `LinearMap.prod`. Primality of $q$ enters as a hypothesis `Fact q.Prime`. Nonvanishing and non-proportionality are stated for the vectors cast to $\mathbb Q^{\iota}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/FiniteRank.lean#L265-L301

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uK uV uι uW uJ
open scoped BigOperators
open Finset

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.integer_rows_eventual_pair_rank {ι : Type uι} {J : Type uJ} [Fintype ι] [Fintype J]
    (a : J → ι → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ)) ≠ 0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ)) ≠ c • (fun k ↦ (a j k : ℚ))) :
    ∃ Q : ℕ, ∀ q : ℕ, ∀ (_hq : Fact q.Prime), Q<q →
      ∀ j l, j≠l → Function.Surjective
        ((dotForm (fun k ↦ (a j k : ZMod q))).prod
         (dotForm (fun k ↦ (a l k : ZMod q)))) := by sorry
