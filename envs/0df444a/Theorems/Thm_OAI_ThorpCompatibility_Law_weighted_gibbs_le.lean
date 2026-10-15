-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_weighted_gibbs_le
-- name    : OAI.ThorpCompatibility.Law.weighted_gibbs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:12:08.317217+00:00
-- url     : https://prove2.me/theorems/58fcbb3f-fedc-48f5-9772-488850ecf607
-- title:
--   Gibbs inequality with exponent $\theta$: log-weight mean minus $\theta$ times the deficit is at most $\log M_\theta(w)$
-- statement:
--   Let $\Omega$ be a nonempty finite set, $P$ a probability law on $\Omega$, $\theta>0$, and $w:\Omega\to[0,\infty)$ a nonnegative weight that is positive wherever $P$ is, i.e. $w(x)=0\Rightarrow P(x)=0$. Let $\Delta(P)=\log|\Omega|-\mathrm{Ent}(P)$ be the uniform deficit of $P$, where $\mathrm{Ent}(P)=-\sum_xP(x)\log P(x)$, and let
--   $$
--   M_\theta(w)=\Big(\frac1{|\Omega|}\sum_{x\in\Omega}w(x)^{1/\theta}\Big)^{\theta}
--   $$
--   be the marginal factor of $w$. Then
--   $$
--   \mathbb{E}_P[\log w]-\theta\,\Delta(P)\le\log M_\theta(w).
--   $$
--
--   For $\theta=1$ this is the Gibbs variational inequality $\mathbb{E}_P[\log w]-\Delta(P)\le\log\big(\frac1{|\Omega|}\sum_xw(x)\big)$. For $0<\theta<1$ the deficit enters with the smaller coefficient $\theta$, at the price of replacing the uniform mean of $w$ by the power mean $M_\theta(w)$. In the weighted compatibility bound it is applied to the marginal laws of each row $r_i$ and each column $c_k$ of the tilted law, with $\theta=1-L/\log m$, and it produces the factors $M_\theta(w_i)$ and $M_\theta(v_k)$.
--
--   **Formalization Note** $M_\theta(w)$ is `marginalFactor θ w`, built from `uniformMean` and `Real.rpow`, and $\mathbb{E}_P[\log w]$ is `P.mean (fun x => Real.log (w x))`. Lean's convention $\log0=0$ is harmless here, since points with $w(x)=0$ have $P(x)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/WeightedGibbs.lean#L38-L67

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

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem OAI.ThorpCompatibility.Law.weighted_gibbs_le [Nonempty α] (P : Law α) {θ : ℝ} (hθ : 0 < θ)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (w x)) - θ*P.uniformDeficit ≤
      Real.log (marginalFactor θ w) := by sorry
