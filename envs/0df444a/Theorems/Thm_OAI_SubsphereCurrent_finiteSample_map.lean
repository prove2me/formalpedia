-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_finiteSample_map
-- name    : OAI.SubsphereCurrent.finiteSample_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:43:23.513827+00:00
-- url     : https://prove2.me/theorems/6ae0f391-69a4-4b85-973a-94cc5e697924
-- title:
--   Inverse-CDF sampling turns a uniform variable on $[0,1)$ into the prescribed finite law
-- statement:
--   Let $n\ge1$ and let $p$ be a probability mass function on $[n]=\{0,1,\dots,n-1\}$, with cumulative sums $F_p(k)=\sum_{0\le j<\min(k,n)}p(j)$. The inverse-CDF sampler $S_p:\mathbb{R}\to[n]$ sends $r$ to an index $j$ with $F_p(j)\le r<F_p(j+1)$ if one exists, and to $0$ otherwise. Let $\lambda_{[0,1)}$ be the uniform distribution on $[0,1)$, that is, Lebesgue measure restricted to $[0,1)$.
--
--   **Theorem.** The image of $\lambda_{[0,1)}$ under $S_p$ is the distribution $p$:
--   $$
--   (S_p)_{\#}\,\lambda_{[0,1)}=\sum_{i=0}^{n-1}p(i)\,\delta_i,\qquad\text{equivalently}\qquad \lambda\bigl(\{r\in[0,1):\ S_p(r)=i\}\bigr)=p(i)\ \text{ for every } i\in[n].
--   $$
--
--   This is exact inverse-transform sampling for finite distributions: if $U$ is uniform on $[0,1)$, then $S_p(U)$ has law $p$. It is the device used to replace every random transition of a finite-state procedure by a deterministic function of an independent uniform coin.
--
--   **Formalization Note** The statement is the equality of measures `coinLaw.map (finiteSample p) = p.toMeasure`, where `coinLaw` is `volume.restrict (Ico 0 1)` and `p.toMeasure` is the measure on `Fin n` attached to the PMF; the instance `[NeZero n]` encodes $n\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L229-L258

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision

open OAI OAI.SubsphereCurrent
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem OAI.SubsphereCurrent.finiteSample_map {n : ℕ} [NeZero n] (p : PMF (Fin n)) :
    coinLaw.map (finiteSample p) = p.toMeasure := by sorry
