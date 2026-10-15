-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_grid_deficit_decomposition
-- name    : OAI.ThorpCompatibility.grid_deficit_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:04:14.162349+00:00
-- url     : https://prove2.me/theorems/7349a753-1d72-492f-ae87-d02927d14116
-- title:
--   The uniform deficit of a grid law splits into marginal deficits plus the row-column dependence
-- statement:
--   Let $Q$ be a probability law on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, where $r=(r_i)_{i\in[A]}$ are row permutations $r_i\in S_D$ and $c=(c_k)_{k\in[D]}$ are column permutations $c_k\in S_A$ (here $[n]=\{0,\dots,n-1\}$ and $S_n$ is the group of permutations of $[n]$). For a law $P$ on a finite set $\Omega$ write $\mathrm{Ent}(P)=-\sum_{x}P(x)\log P(x)$ for its Shannon entropy and $\Delta(P)=\log|\Omega|-\mathrm{Ent}(P)$ for its uniform deficit, the relative entropy of $P$ with respect to the uniform law on $\Omega$. Let $Q_r$ be the law of the row block $r$ on $(S_D)^{[A]}$ and $Q_{c_k}$ the law of the column $c_k$ on $S_A$. Then
--   $$
--   \Delta(Q)=\Delta(Q_r)+\sum_{k\in[D]}\Delta(Q_{c_k})+\Big(\mathrm{Ent}(Q_r)+\sum_{k\in[D]}\mathrm{Ent}(Q_{c_k})-\mathrm{Ent}(Q)\Big).
--   $$
--
--   The identity splits the distance of $Q$ from the uniform law into the deficits of its marginals and the dependence term in parentheses, the total correlation of $r,c_0,\dots,c_{D-1}$. In the weighted compatibility argument, the dependence term is bounded from below by $AD$ minus small losses, while the marginal deficits are traded against the row and column weights.
--
--   **Formalization Note** $\Delta$ is `Law.uniformDeficit`, defined as $\log|\Omega|+\sum_xP(x)\log P(x)$, and the marginals are the push-forwards `Q.map Prod.fst` and `Q.map (fun a => a.2 k)`. The identity holds for every law $Q$; no compatibility assumption is made.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ExposureEntropy.lean#L109-L129

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

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.grid_deficit_decomposition {A D : ℕ} (Q : Law (Grid A D)) :
    Q.uniformDeficit = (Q.map Prod.fst).uniformDeficit +
      (∑ k : Fin D, (Q.map (fun a => a.2 k)).uniformDeficit) +
        ((Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy) := by sorry
