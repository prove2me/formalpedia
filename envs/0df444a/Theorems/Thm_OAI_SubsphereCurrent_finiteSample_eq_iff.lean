-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_finiteSample_eq_iff
-- name    : OAI.SubsphereCurrent.finiteSample_eq_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:42:11.311139+00:00
-- url     : https://prove2.me/theorems/5b89d661-7495-4794-a0e0-e04fc41bcb6e
-- title:
--   Level sets of the inverse-CDF sampler on a finite set
-- statement:
--   Let $n\ge 1$ and let $p$ be a probability mass function on $[n]=\{0,1,\dots,n-1\}$. Its cumulative sums are $F_p(k)=\sum_{0\le j<\min(k,n)}p(j)$ for $k\in\mathbb{N}$, so that $F_p(0)=0$ and $F_p(i+1)=F_p(i)+p(i)$ for $i<n$. The *inverse-CDF sampler* $S_p:\mathbb{R}\to[n]$ sends $r$ to an index $j\in[n]$ with $F_p(j)\le r<F_p(j+1)$ if such an index exists, and to $0$ otherwise.
--
--   **Theorem.** For every $i\in[n]$ and every $r\in\mathbb{R}$,
--   $$
--   S_p(r)=i\iff\Bigl(F_p(i)\le r<F_p(i+1)\Bigr)\ \text{ or }\ \Bigl(i=0\ \text{ and there is no } j\in[n]\text{ with } F_p(j)\le r<F_p(j+1)\Bigr).
--   $$
--
--   Thus the fibre $S_p^{-1}(i)$ is the half-open interval $[F_p(i),F_p(i+1))$, and for $i=0$ it additionally contains every $r$ lying in none of these intervals (as the intervals tile $[0,1)$, these are exactly the $r\notin[0,1)$). In particular, the possibly arbitrary choice in the definition of $S_p$ never matters. This explicit description of the fibres is the basic tool for showing that the sampler is measurable and that it turns a uniform random variable on $[0,1)$ into a random element of $[n]$ with law $p$.
--
--   **Formalization Note** The cumulative sums are `finiteCDF p k`, which add the real numbers `(p j).toReal` because PMF values live in $[0,\infty]$; the sampler `finiteSample p r` picks its index with `Classical.choose`. The assumption $n\ge1$ is the instance `[NeZero n]`, which makes the default value $0$ available.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L176-L195

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

theorem OAI.SubsphereCurrent.finiteSample_eq_iff {n : ℕ} [NeZero n] (p : PMF (Fin n)) (i : Fin n) (r : ℝ) :
    finiteSample p r = i ↔
      (finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)) ∨
      (i = 0 ∧ ¬ ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1)) := by sorry
