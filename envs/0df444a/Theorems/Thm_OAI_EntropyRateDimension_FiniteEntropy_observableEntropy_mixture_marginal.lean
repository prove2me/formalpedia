-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_observableEntropy_mixture_marginal
-- name    : OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_marginal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:05:20.982607+00:00
-- url     : https://prove2.me/theorems/7938424c-99df-4f88-967a-8b1cee99b1c7
-- title:
--   Marginal entropy of a mixture
-- statement:
--   Let $t$ and $s$ be finite sets, $w$ weights on $t$, and $p_i$ weights on $s$ for each $i\in t$. Consider the product weights $w_ip_i(a)$ on $t\times s$ and an observable $f$ of the second coordinate. Then
--   $$
--   H_{t\times s}\bigl((i,a)\mapsto f(a)\bigr)=H_s\Bigl(f;\ a\mapsto\sum_{i\in t}w_ip_i(a)\Bigr).
--   $$
--
--   The entropy of an observable of the second coordinate depends only on the mixture of the laws $p_i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L779-L794

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_marginal {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => f ia.2) =
      observableEntropy s (fun a => ∑ i ∈ t, w i*p i a) f := by sorry
