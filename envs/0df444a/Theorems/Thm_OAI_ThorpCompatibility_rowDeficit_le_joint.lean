-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_rowDeficit_le_joint
-- name    : OAI.ThorpCompatibility.rowDeficit_le_joint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:09:03.409047+00:00
-- url     : https://prove2.me/theorems/b9f945b0-9703-4876-b8ba-b63844d9f42b
-- title:
--   The sum of the single-row deficits is at most the deficit of the joint row law
-- statement:
--   Let $Q$ be a probability law on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, where $r=(r_i)_{i\in[A]}$ are row permutations $r_i\in S_D$ and $c=(c_k)_{k\in[D]}$ are column permutations $c_k\in S_A$ (here $[n]=\{0,\dots,n-1\}$ and $S_n$ is the group of permutations of $[n]$). For a law $P$ on a finite set $\Omega$ write $\mathrm{Ent}(P)=-\sum_{x}P(x)\log P(x)$ for its Shannon entropy and $\Delta(P)=\log|\Omega|-\mathrm{Ent}(P)$ for its uniform deficit, the relative entropy of $P$ with respect to the uniform law on $\Omega$. Let $Q_{r_i}$ be the law of the single row $r_i$ on $S_D$ and $Q_r$ the joint law of the row block $r=(r_i)_{i\in[A]}$ on $(S_D)^{[A]}$. Then
--   $$
--   \sum_{i\in[A]}\Delta(Q_{r_i})\le\Delta(Q_r).
--   $$
--
--   This is subadditivity of entropy written for deficits: the deficit of a joint law dominates the total deficit of its one-row marginals, with equality when the rows are independent. In the entropy estimate for compatible grids, the clump losses are charged to the joint row deficit $\Delta(Q_r)$, while the Gibbs step against the row weights $w_i(r_i)$ uses the individual deficits $\Delta(Q_{r_i})$; this inequality connects the two.
--
--   **Formalization Note** The two sides are `rowDeficit Q` and `jointRowDeficit Q`, defined through `Law.uniformDeficit` of the push-forwards `Q.map (fun a => a.1 i)` and `Q.map Prod.fst`. The columns of the grid play no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/GridDeficits.lean#L36-L48

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

theorem OAI.ThorpCompatibility.rowDeficit_le_joint {A D : ℕ} (Q : Law (Grid A D)) :
    rowDeficit Q ≤ jointRowDeficit Q := by sorry
