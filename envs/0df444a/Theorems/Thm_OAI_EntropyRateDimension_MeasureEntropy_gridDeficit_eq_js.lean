-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_gridDeficit_eq_js
-- name    : OAI.EntropyRateDimension.MeasureEntropy.gridDeficit_eq_js
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:15:38.92337+00:00
-- url     : https://prove2.me/theorems/f4c9f479-9823-4c56-8651-1208b9edc885
-- title:
--   The grid deficit is a Jensen–Shannon divergence
-- statement:
--   For a probability measure $\mu$ on $\mathbb R$, a mesh $s>0$ and a shift $u$, the grid label is $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, the grid entropy $H_{s,u}(\mu)=\sum_j-m_j\log m_j$ is the entropy of the masses $m_j=\mu\{\ell_{s,u}=j\}$, and the averaged grid entropy is $\bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du$. A measure is compactly carried if it vanishes outside some interval $[-B,B]$.
--
--   Let $\mu$ be compactly carried, $s>0$, $u$ a shift, and $p$ the finite law of $\ell_{s,u}$ under $\mu$, a distribution on $\mathbb Z$. The grid deficit, the entropy gained by the fair shift $\frac12(\mu+\mu(\cdot-s))$ at mesh $s$, satisfies
--   $$
--   H_{s,u}\Bigl(\tfrac12(\mu+\mu(\cdot-s))\Bigr)-H_{s,u}(\mu)=\mathrm{JS}\bigl(p,\ p(\cdot-1)\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L994-L1009

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.MeasureEntropy.gridDeficit_eq_js (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    gridDeficit μ s u=(gridLaw μ hμ hs u).js ((gridLaw μ hμ hs u).translate 1) := by sorry
