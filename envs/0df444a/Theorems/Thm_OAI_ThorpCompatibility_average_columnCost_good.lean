-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_average_columnCost_good
-- name    : OAI.ThorpCompatibility.average_columnCost_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:56:07.908255+00:00
-- url     : https://prove2.me/theorems/465948ad-cf7a-49a5-8b23-4a55712eb467
-- title:
--   Random-order lower bound for the exposure cost of a light column entry in a small clump
-- statement:
--   Work on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, where $r=(r_i)_{i\in[A]}$ are row permutations $r_i\in S_D$ and $c=(c_k)_{k\in[D]}$ are column permutations $c_k\in S_A$; here $[n]=\{0,\dots,n-1\}$ and $S_n$ is the group of permutations of $[n]$. The pair $a$ is *compatible* if for every slot $j\in[D]$ the map $h\mapsto c_{r_h(j)}(h)$ is injective on $[A]$.
--
--   Let $Q$ be a probability law on $\mathcal G_{A,D}$, fix a column $k\in[D]$ and a row index $i\in[A]$, and let $H\ge 0$ and $K$ be real numbers. For a configuration $a$ let $\widehat Q$ be the conditional law under $Q$ of the entry $c_k(i)$ given the column history $\mathrm{ch}_{k,i}(a)$, i.e. given the values $c_k(0),\dots,c_k(i-1)$ of $a$, and let
--   $$
--   \Lambda=\Big\{w\in[A]:\ \widehat Q(w)\le\frac{H}{A-i}\Big\}
--   $$
--   be the set of light values. For a column order $e\in S_D$ put $j=r_i^{-1}(k)$ and let $\mathcal A_e=\{w\in[A]: w\ne c_{r_h(j)}(h)\text{ for every row }h\text{ with }e(r_h(j))<e(k)\}$ be the set of values still allowed for the entry once the rows and the columns preceding $k$ in the order $e$ are known. The column cost is
--   $$
--   \mathrm{cost}_{e,k,i}(a)=-\log\frac{\widehat Q(\Lambda\cap\mathcal A_e)}{\widehat Q(\Lambda)}\ \text{ if }c_k(i)\in\Lambda,\qquad \mathrm{cost}_{e,k,i}(a)=0\ \text{ otherwise.}
--   $$
--   Let $\mathrm{cs}_{k,i}(a)=|\{h\in[A]: r_h(j)=k\}|$ be the clump size of the entry, and let
--   $$
--   \mathrm{err}_{A,D}(H,K;i)=\frac{1+\log D}{D}+\frac{2KH}{A-i}\,(1+\log D).
--   $$
--
--   **Theorem.** Assume $D\ge 2$, and let $a=(r,c)$ be a compatible configuration with $Q(a)>0$ such that
--
--   1. the light values carry at least half of the predicted mass, $\widehat Q(\Lambda)\ge\frac12$;
--   2. the actual value is light, $c_k(i)\in\Lambda$;
--   3. the clump size is bounded, $\mathrm{cs}_{k,i}(a)\le K$.
--
--   Then, on average over a uniformly random column order,
--   $$
--   1-\mathrm{err}_{A,D}(H,K;i)\le\frac{1}{D!}\sum_{e\in S_D}\mathrm{cost}_{e,k,i}(a).
--   $$
--
--   The column cost is a lower bound for the entropy that is saved at the entry $c_k(i)$ when one conditions on the full past (rows and earlier columns) instead of on the column history alone. The theorem therefore says that a good entry saves at least $1-\mathrm{err}_{A,D}(H,K;i)$ nats on average over column orders. This is the main case of the entropy estimate for laws on compatible grids; entries that violate one of the three conditions are charged to the heavy mass or to the clump count instead.
--
--   **Formalization Note** $\widehat Q$ is `columnPrediction Q k i (colHistory k i a)`, $\Lambda$ is `columnLight`, $\mathcal A_e$ is `gridAllowed k i (gridPast e k i a)`, $\mathrm{cs}_{k,i}$ is `entryClumpSize` and $\mathrm{err}$ is `exposureError`. The average over $e$ is the mean under `Law.uniform` on `Equiv.Perm (Fin D)`. The number $A-i$ is a natural-number subtraction cast to $\mathbb{R}$; it equals $A-i\ge1$ because $i<A$. No sign condition on $K$ is imposed (hypothesis 3 forces $K\ge0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ClumpCost.lean#L58-L109

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

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.average_columnCost_good {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (a : Grid A D) (hQa : 0 < Q.mass a) (ha : Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (k : Fin D) (i : Fin A)
    (hL : 1/2 ≤ (columnPrediction Q k i (colHistory k i a)).prob
      (columnLight Q H k i (colHistory k i a)))
    (haL : columnLight Q H k i (colHistory k i a) (a.2 k i))
    (hK : (entryClumpSize k i a : ℝ) ≤ K) :
    1 - exposureError A D H K i ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => columnCost Q H e k i a) := by sorry
