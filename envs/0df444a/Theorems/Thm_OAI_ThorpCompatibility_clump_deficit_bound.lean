-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_clump_deficit_bound
-- name    : OAI.ThorpCompatibility.clump_deficit_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:09:34.923565+00:00
-- url     : https://prove2.me/theorems/18685fc4-818e-4dae-9e5a-84b152c3f768
-- title:
--   The mean clump count of the rows is controlled by the joint row deficit
-- statement:
--   Let $Q$ be a probability law on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, with row permutations $r=(r_i)_{i\in[A]}$, $r_i\in S_D$, and column permutations $c_k\in S_A$. For a row family $r$ and a real threshold $K$ let
--   $$
--   \mathrm{clump}_K(r)=\sum_{(j,k)\in[D]^2}|C_{jk}|\;\mathbf 1\big[|C_{jk}|>K\big],\qquad C_{jk}=\{i\in[A]:\ r_i(j)=k\},
--   $$
--   be the clump count. Let $\Delta(Q_r)=\log|(S_D)^{[A]}|-\mathrm{Ent}(Q_r)$ be the uniform deficit of the law $Q_r$ of the row block under $Q$. Let $m$ be a real number for which the clump moment bound
--   $$
--   \mathbb{E}_{\bar r}\Big[\exp\Big(\frac{\log m}{400}\;\mathrm{clump}_{m^{1/100}}(\bar r)\Big)\Big]\le2
--   $$
--   holds, where $\bar r$ is uniform on $(S_D)^{[A]}$. Then
--   $$
--   \log m\cdot\mathbb{E}_{a\sim Q}\big[\mathrm{clump}_{m^{1/100}}(r)\big]\le400\,\Delta(Q_r)+400 .
--   $$
--
--   The hypothesis concerns uniformly random rows only; the conclusion transfers it to an arbitrary law $Q$, at the price of the deficit of its row law. This is how the clump losses in the entropy estimate for compatible grids are absorbed into the row deficit, which is then paid for by the marginal factors.
--
--   **Formalization Note** $\Delta(Q_r)$ is `jointRowDeficit Q`, the average over $\bar r$ is `uniformMean` over `Rows A D`, and `clumpCount` is a natural number cast to $\mathbb{R}$. The theorem is stated for every real $m$, with Mathlib's conventions for `Real.log` and `Real.rpow` when $m\le0$; it is applied with $\log m\ge1000$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/GridDeficits.lean#L50-L70

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
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridDeficits

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.clump_deficit_bound {A D : ℕ} (Q : Law (Grid A D)) (m : ℝ)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2) :
    Real.log m * Q.mean (fun a => (clumpCount (m^(1/100:ℝ)) a.1 : ℝ)) ≤
      400 * jointRowDeficit Q + 400 := by sorry
