-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_grid_entropy_charge
-- name    : OAI.ThorpCompatibility.grid_entropy_charge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:03:15.51861+00:00
-- url     : https://prove2.me/theorems/ad752227-8e75-4e7e-8bf3-08b2339c8f21
-- title:
--   Rows and columns of a compatible grid law share at least $AD$ nats, up to exposure, heavy-mass and clump losses
-- statement:
--   Let $Q$ be a probability law on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, where $r=(r_i)_{i\in[A]}$ are row permutations $r_i\in S_D$ and $c=(c_k)_{k\in[D]}$ are column permutations $c_k\in S_A$ (here $[n]=\{0,\dots,n-1\}$ and $S_n$ is the group of permutations of $[n]$). For a law $P$ on a finite set $\Omega$ write $\mathrm{Ent}(P)=-\sum_{x}P(x)\log P(x)$ for its Shannon entropy and $\Delta(P)=\log|\Omega|-\mathrm{Ent}(P)$ for its uniform deficit, the relative entropy of $P$ with respect to the uniform law on $\Omega$. The pair $a$ is *compatible* if for every $j\in[D]$ the map $h\mapsto c_{r_h(j)}(h)$ is injective. Write $\mathrm{Ent}_Q(r)$ and $\mathrm{Ent}_Q(c_k)$ for the entropies of the laws of $r$ and of $c_k$ under $Q$, and $\mathrm{Ent}(Q)$ for the entropy of $Q$ itself.
--
--   The loss terms are the following.
--
--   1. *Heavy mass.* For $H\in\mathbb{R}$, $\mathrm{HT}_H(Q)=\sum_{k\in[D]}\sum_{i\in[A]}\mathbb{E}_{a\sim Q}[\mathrm{hm}_{k,i}(a)]$. Here $\mathrm{hm}_{k,i}(a)$ is the conditional probability under $Q$, given that $c_k(0),\dots,c_k(i-1)$ take their values in $a$, of the set of values $w\in[A]$ whose own conditional probability exceeds $H/(A-i)$.
--   2. *Clump count.* For $K\in\mathbb{R}$, $\mathrm{clump}_K(r)=\sum_{(j,k)\in[D]^2}|C_{jk}|\,\mathbf 1[|C_{jk}|>K]$, where $C_{jk}=\{i\in[A]: r_i(j)=k\}$.
--   3. *Exposure error.* $E_{A,D}(H,K)=A(1+\log D)+2DKH(1+\log D)\,\mathcal H_A$, where $\mathcal H_A=\sum_{t=1}^{A}\frac1t$ is the $A$-th harmonic number.
--
--   **Theorem.** Let $D\ge2$, let $Q$ be supported on compatible pairs (every $a$ with $Q(a)>0$ is compatible), and let $H\ge0$ and $K\ge0$. Then
--   $$
--   AD-E_{A,D}(H,K)-3\,\mathrm{HT}_H(Q)-\mathbb{E}_{a\sim Q}\big[\mathrm{clump}_K(r)\big]\le\mathrm{Ent}_Q(r)+\sum_{k\in[D]}\mathrm{Ent}_Q(c_k)-\mathrm{Ent}(Q).
--   $$
--
--   The right side measures the dependence between the row block $r$ and the columns $c_0,\dots,c_{D-1}$ under $Q$; it vanishes when they are independent. The theorem says that compatibility forces this dependence to be large: one nat for each of the $AD$ column entries, minus the three losses. Together with the decomposition of $\Delta(Q)$ into marginal deficits plus this dependence term, it yields the entropy estimate behind the weighted compatibility bound, in which the heavy mass and the clump count are afterwards absorbed into the column and row deficits.
--
--   **Formalization Note** The entropies are `(Q.map Prod.fst).entropy`, `(Q.map (fun a => a.2 k)).entropy` and `Q.entropy`. The heavy mass is `entryHeavyMass Q H k i`, the clump count is `clumpCount K a.1` (a natural number cast to $\mathbb{R}$), and $E_{A,D}$ is `totalExposureError A D H K`, which uses Mathlib's `harmonic A`. The heavy-mass threshold $H$ and the clump threshold $K$ are independent parameters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ExposureEntropy.lean#L80-L107

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

theorem OAI.ThorpCompatibility.grid_entropy_charge {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) :
    (A : ℝ) * D - totalExposureError A D H K -
      3 * (∑ k : Fin D, ∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)) -
      Q.mean (fun a => (clumpCount K a.1 : ℝ)) ≤
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy := by sorry
