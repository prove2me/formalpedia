-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_compatibilityWeight_support
-- name    : OAI.ThorpCompatibility.compatibilityWeight_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:16:17.155762+00:00
-- url     : https://prove2.me/theorems/61bc2a5c-68c1-47df-a278-d2d816de4dd0
-- title:
--   Positive compatibility weight forces compatibility and positive row and column weights
-- statement:
--   Let $A$ and $D$ be natural numbers, write $[A]=\{0,\dots,A-1\}$ and $[D]=\{0,\dots,D-1\}$, and let $S_n$ be the group of permutations of $[n]$. A grid point is a pair $(r,c)$ consisting of row permutations $r_i\in S_D$ for $i\in[A]$ and column permutations $c_k\in S_A$ for $k\in[D]$. The pair is *compatible* if for every $j\in[D]$ the map $i\mapsto c_{r_i(j)}(i)$ is injective on $[A]$.
--
--   Let $w_i:S_D\to\mathbb{R}$ $(i\in[A])$ and $v_k:S_A\to\mathbb{R}$ $(k\in[D])$ be weight functions with $w_i(\sigma)\ge 0$ and $v_k(\tau)\ge 0$ for all indices and all permutations $\sigma\in S_D$, $\tau\in S_A$. The compatibility weight of a grid point is
--   $$
--   \omega(r,c)=\begin{cases}\displaystyle\prod_{i\in[A]}w_i(r_i)\prod_{k\in[D]}v_k(c_k), & (r,c)\text{ compatible},\\ 0, & \text{otherwise.}\end{cases}
--   $$
--   If $\omega(r,c)>0$, then:
--
--   1. the pair $(r,c)$ is compatible;
--   2. $w_i(r_i)>0$ for every $i\in[A]$;
--   3. $v_k(c_k)>0$ for every $k\in[D]$.
--
--   In other words, the support of $\omega$ consists of compatible pairs at which every row and column factor is strictly positive. Consequently, when the total weight is positive, the Gibbs law $Q(r,c)=\omega(r,c)/\sum\omega$ charges only compatible pairs, and on its support $\log\omega(r,c)=\sum_i\log w_i(r_i)+\sum_k\log v_k(c_k)$; moreover the law of each $r_i$ (resp. $c_k$) under $Q$ is supported where $w_i>0$ (resp. $v_k>0$). These facts are what allow the entropy method to split the weight into row and column contributions.
--
--   **Formalization Note** A grid point is `a : Grid A D`, where `Grid A D` abbreviates `Rows A D × Cols A D`, with `a.1` the row family and `a.2` the column family. The weight `compatibilityWeight w v a` is defined by an `if` on `Compatible a.1 a.2`, returning the product of the row and column weights in the compatible case and $0$ otherwise. If $A=0$ or $D=0$ the corresponding product is empty (equal to $1$) and the corresponding claim is vacuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/VariationalBound.lean#L42-L62

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
import Definitions.Def_OAI_Probability_ThorpCompatibility_VariationalBound

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.compatibilityWeight_support {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    {a : Grid A D} (ha : 0 < compatibilityWeight w v a) :
    Compatible a.1 a.2 ∧ (∀ i, 0 < w i (a.1 i)) ∧ (∀ k, 0 < v k (a.2 k)) := by sorry
