-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_kl_tilt_le
-- name    : OAI.ThresholdParallelRepetition.FiniteProbability.Law.kl_tilt_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:57:33.655027+00:00
-- url     : https://prove2.me/theorems/aef96b65-7b29-484a-a191-877255fd8923
-- title:
--   Relative entropy of a tilt by a density bounded by $B$ is at most $\log B$
-- statement:
--   Let $\alpha$ be a finite set and let $p$ be a probability distribution on $\alpha$, given by weights $p(x)\ge0$ with $\sum_{x}p(x)=1$. Let $f:\alpha\to\mathbb{R}$ be a probability density with respect to $p$, that is, $f(x)\ge0$ for all $x$ and $\mathbb{E}_p[f]=\sum_xp(x)f(x)=1$, and let $p_f$ be the tilted distribution with weights $p_f(x)=p(x)f(x)$. If $B>0$ and $f(x)\le B$ for every $x\in\alpha$, then
--
--   $$
--   D(p_f\,\|\,p)=\sum_{x\in\alpha}p_f(x)\log\frac{p_f(x)}{p(x)}\;\le\;\log B .
--   $$
--
--   A change of measure whose density is bounded by $B$ costs at most $\log B$ in relative entropy. For example, conditioning $p$ on an event $E\subseteq\alpha$ with $p(E)=\beta>0$ corresponds to the density $f=\mathbf 1_E/\beta\le1/\beta$, so the conditioned law has relative entropy at most $\log(1/\beta)$ with respect to $p$.
--
--   **Formalization Note** The relative entropy `kl` is defined as $\sum_xq(x)\log(q(x)/p(x))$ with Lean's conventions $\log0=0$ and $r/0=0$; for $q=p_f$ every point with $p(x)=0$ also has $p_f(x)=0$, so this agrees with the usual definition. The hypothesis $B>0$ is part of the statement but is not used in the proof (it also follows from $1=\mathbb{E}_p[f]\le B$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/FiniteProbability.lean#L331-L344

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Law
universe u_α u_β u_γ u_E u_F u_ι
open scoped BigOperators
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]

omit [DecidableEq α] in
theorem OAI.ThresholdParallelRepetition.FiniteProbability.Law.kl_tilt_le (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1)
    {B : ℝ} (_hB : 0 < B) (hb : ∀ x, f x ≤ B) : (p.tilt f hf ht).kl p ≤ Real.log B := by sorry
