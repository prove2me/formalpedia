-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_clump_exp_moment_le
-- name    : OAI.ThorpCompatibility.clump_exp_moment_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:01:18.638055+00:00
-- url     : https://prove2.me/theorems/7bd156c4-dad8-4fca-b807-97ac7b1dca14
-- title:
--   Product-over-cells bound for the exponential moment of the clump count of uniform row permutations
-- statement:
--   Let $I$ and $J$ be finite sets with $n=|J|\ge1$, and let $r=(r_i)_{i\in I}$ be a family of permutations of $J$. For a cell $(j,k)\in J\times J$ let $C_{jk}(r)=\{i\in I: r_i(j)=k\}$ be the set of rows through it, and for a real threshold $H$ let
--   $$
--   \mathrm{clump}_H(r)=\sum_{(j,k)\in J\times J}|C_{jk}(r)|\;\mathbf 1\big[|C_{jk}(r)|>H\big]
--   $$
--   be the clump count, the number of row incidences lying in cells met by more than $H$ rows. For $z\in\mathbb{R}$ and $s\subseteq I$ define the clump weight $\phi_{H,z}(s)=1$ if $s=\varnothing$, $\phi_{H,z}(s)=e^{z|s|}$ if $s\ne\varnothing$ and $|s|>H$, and $\phi_{H,z}(s)=0$ otherwise.
--
--   If $H\ge0$ and $z\in\mathbb{R}$, then for $r$ uniform on $(S_J)^I$,
--   $$
--   \mathbb{E}_r\Big[e^{z\,\mathrm{clump}_H(r)}\Big]\le\Bigg(\sum_{s\subseteq I}\phi_{H,z}(s)\Big(\frac{e}{n}\Big)^{|s|}\Bigg)^{n^2}.
--   $$
--
--   The right side is a single one-cell sum raised to the power $n^2$, the number of cells, so the cells are handled as if they were independent. Evaluating the one-cell sum by subset size then gives an explicit bound on the moment generating function of the clump count. This is how large clumps of rows are shown to be rare under uniformly random rows in the entropy estimate for compatible grids.
--
--   **Formalization Note** The average is `uniformMean` over all functions `α → Equiv.Perm β`, `clumpCount H r` is a natural number cast to $\mathbb{R}$, $\phi_{H,z}$ is `clumpWeight H z`, and the inner sum ranges over all `s : Finset α`. No sign condition on $z$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ClumpMoments.lean#L67-L104

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

theorem OAI.ThorpCompatibility.clump_exp_moment_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      (∑ s : Finset α, clumpWeight H z s *
        (Real.exp 1 / Fintype.card β) ^ s.card) ^ (Fintype.card β ^ 2) := by sorry
