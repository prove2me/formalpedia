-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_weightedCompatibility_bound
-- name    : OAI.ThorpCompatibility.weightedCompatibility_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:17:40.939788+00:00
-- url     : https://prove2.me/theorems/5ac4a352-6635-4e7e-a1b7-826167453038
-- title:
--   Weighted compatibility bound with explicit constants under a clump moment hypothesis
-- statement:
--   Let $A,D$ be natural numbers, $[A]=\{0,\dots,A-1\}$, $[D]=\{0,\dots,D-1\}$, and $S_n$ the group of permutations of $[n]$. A pair $(r,c)$ consists of row permutations $r_i\in S_D$ $(i\in[A])$ and column permutations $c_k\in S_A$ $(k\in[D])$; it is *compatible* if for every $j\in[D]$ the map $i\mapsto c_{r_i(j)}(i)$ is injective on $[A]$. Throughout, $\mathbb{E}$ denotes the uniform average over the indicated finite set.
--
--   For weight families $w=(w_i)_{i\in[A]}$ with $w_i:S_D\to\mathbb{R}$ and $v=(v_k)_{k\in[D]}$ with $v_k:S_A\to\mathbb{R}$, the *weighted compatibility* is
--   $$
--   W_{A,D}(w,v)=\frac{(AD)!}{(D!)^A\,(A!)^D}\;\mathbb{E}_{(r,c)\in S_D^{[A]}\times S_A^{[D]}}\Big[\mathbf 1[(r,c)\text{ compatible}]\prod_{i\in[A]}w_i(r_i)\prod_{k\in[D]}v_k(c_k)\Big].
--   $$
--   For $\theta>0$ and a function $u\ge 0$ on a finite set $X$, the *marginal factor* is $M_\theta(u)=\big(\mathbb{E}_{x\in X}\,u(x)^{1/\theta}\big)^{\theta}$. For a row family $r\in S_D^{[A]}$ and a cell $(j,k)\in[D]\times[D]$, let $N_{jk}(r)=|\{i\in[A]:r_i(j)=k\}|$, and for a threshold $H\in\mathbb{R}$ let
--   $$
--   \mathrm{clump}_H(r)=\sum_{(j,k)\in[D]\times[D]}N_{jk}(r)\,\mathbf 1[N_{jk}(r)>H]
--   $$
--   be the number of row incidences lying in cells that are hit by more than $H$ rows.
--
--   **Theorem.** Let $m$ be a real number such that
--   $$
--   m\ge 4,\qquad m^2=AD,\qquad \log m\ge 1000,\qquad \theta:=1-\frac{1000}{\log m}>0,
--   $$
--   and suppose that $m/2\le A\le 2m$ and $m/2\le D\le 2m$. Assume the clump moment bound
--   $$
--   \mathbb{E}_{r\in S_D^{[A]}}\exp\Big(\frac{\log m}{400}\,\mathrm{clump}_{m^{1/100}}(r)\Big)\le 2 .
--   $$
--   Then for all weight families with $w_i(\sigma)\ge 0$ and $v_k(\tau)\ge 0$ for all $i\in[A]$, $k\in[D]$, $\sigma\in S_D$, $\tau\in S_A$,
--   $$
--   W_{A,D}(w,v)\le \exp\big(50000\,(AD)^{54/100}\big)\prod_{i\in[A]}M_\theta(w_i)\prod_{k\in[D]}M_\theta(v_k).
--   $$
--
--   This is the weighted compatibility bound with explicit constants $L=1000$ and $C_0=50000$, in which the input about uniformly random row permutations, an exponential moment bound for the clump count, is isolated as a hypothesis; the weighted compatibility theorem follows once that hypothesis is verified for all sufficiently large $m$. Taking all weights equal to $1$ (so that every marginal factor equals $1$) shows in particular that, under the same hypotheses on $m$, a uniformly random pair $(r,c)$ is compatible with probability at most $e^{50000(AD)^{54/100}}\,(D!)^A(A!)^D/(AD)!$.
--
--   **Formalization Note** The objects are `weightedCompatibility A D w v`, `marginalFactor θ u = (uniformMean (fun x => (u x)^(1/θ)))^θ` (real powers, `uniformMean` being the plain average over a finite type) and `clumpCount H r`, which sums the sizes of the cells $\{i : r_i(j)=k\}$ of size strictly greater than $H$. The parameter $m$ is a real number tied to $A$ and $D$ by $m^2=AD$ rather than defined as $\sqrt{AD}$. The weights are arbitrary real-valued functions on `Equiv.Perm (Fin D)` and `Equiv.Perm (Fin A)`, with nonnegativity as explicit hypotheses, and the assumption $\theta>0$ excludes the boundary case $\log m=1000$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/Main.lean#L30-L107

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

theorem OAI.ThorpCompatibility.weightedCompatibility_bound {A D : ℕ} {m : ℝ}
    (hm : 4 ≤ m) (hmdef : m^2 = (A:ℝ)*D)
    (hl : 1000 ≤ Real.log m) (hθ : 0 < 1-1000/Real.log m)
    (hAl : m/2 ≤ A) (hAu : (A:ℝ) ≤ 2*m)
    (hDl : m/2 ≤ D) (hDu : (D:ℝ) ≤ 2*m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ) :
    weightedCompatibility A D w v ≤
      Real.exp (50000*((A:ℝ)*D)^(54/100:ℝ)) *
        (∏ i, marginalFactor (1-1000/Real.log m) (w i)) *
        (∏ k, marginalFactor (1-1000/Real.log m) (v k)) := by sorry
