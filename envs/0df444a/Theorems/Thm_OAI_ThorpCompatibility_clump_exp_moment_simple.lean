-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_clump_exp_moment_simple
-- name    : OAI.ThorpCompatibility.clump_exp_moment_simple
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:02:16.344151+00:00
-- url     : https://prove2.me/theorems/e6ed10a9-c5f5-4f75-9cc9-d592fe68c5e2
-- title:
--   Explicit moment generating function bound for the clump count of uniform row permutations
-- statement:
--   Let $I$ and $J$ be finite sets with $a=|I|$ and $n=|J|\ge1$. For a family $r=(r_i)_{i\in I}$ of permutations of $J$ and a real threshold $H$, let
--   $$
--   \mathrm{clump}_H(r)=\sum_{(j,k)\in J\times J}|C_{jk}(r)|\;\mathbf 1\big[|C_{jk}(r)|>H\big],\qquad C_{jk}(r)=\{i\in I:\ r_i(j)=k\},
--   $$
--   be the clump count, the number of row incidences lying in cells met by more than $H$ rows. Let $H\ge0$ and $z\in\mathbb{R}$ satisfy the smallness condition
--   $$
--   e^{2}\,a\,e^{z}\,\frac{e}{n}\le H .
--   $$
--   Then, for $r$ uniform on $(S_J)^I$,
--   $$
--   \mathbb{E}_r\Big[e^{z\,\mathrm{clump}_H(r)}\Big]\le\exp\big(n^{2}(a+1)\,e^{-H}\big).
--   $$
--
--   If $a\le2m$ and $m/2\le n\le2m$ for a large real $m$, one may take $H=m^{1/100}$ and $z=\frac1{400}\log m$: the smallness condition then holds, and the right side is at most $2$ once $m$ is large enough. This is how the clump moment hypothesis used in the weighted compatibility bound is verified.
--
--   **Formalization Note** The average is `uniformMean` over all functions `α → Equiv.Perm β`, and `clumpCount H r` is a natural number cast to $\mathbb{R}$. The smallness hypothesis is stated as `exp 2 * card α * (exp z * (exp 1 / card β)) ≤ H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/MomentBound.lean#L10-L36

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem OAI.ThorpCompatibility.clump_exp_moment_simple {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β)
    (hsmall : Real.exp 2 * Fintype.card α *
      (Real.exp z * (Real.exp 1 / Fintype.card β)) ≤ H) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      Real.exp ((Fintype.card β : ℝ) ^ 2 * (Fintype.card α + 1) * Real.exp (-H)) := by sorry
