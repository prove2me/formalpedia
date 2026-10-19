-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_bounds_of_weight
-- name    : OAI.BackwardIntertwiners.bounds_of_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:22:51.23657+00:00
-- url     : https://prove2.me/theorems/c4b84ba4-9d39-4d40-9bf9-2581a374bb8d
-- title:
--   Weight bounds on $b$ and reciprocal-weight bounds on $c$ give envelope bounds with the logarithmic profiles of the weight
-- statement:
--   Let $w:\mathbb{Z}\to\mathbb{R}$ be a weight with $w(j)>0$ for all $j$, and define its logarithmic profiles $P_w,Q_w:\mathbb{N}\to\mathbb{R}$ by
--   $$P_w(n)=\log w(-n),\qquad Q_w(n)=-\log w(n)\qquad(n\in\mathbb{N}).$$
--   Let $b,c:\mathbb{Z}\to\mathbb{C}$ satisfy
--   $$|b_j|\le w(j)\qquad\text{and}\qquad|c_j|\,w(j)\le1\qquad\text{for all }j\in\mathbb{Z}.$$
--   Then for every $n\in\mathbb{N}$,
--   $$|b_n|\le e^{-Q_w(n)},\qquad|b_{-n}|\le e^{P_w(n)},\qquad|c_n|\le e^{Q_w(n)},\qquad|c_{-n}|\le e^{-P_w(n)};$$
--   that is, $(b,c)$ satisfies the envelope bounds with profiles $(P_w,Q_w)$.
--
--   This translates the weighted conditions used to define support separation for a weight $w$ into the profile language of the correlation estimates, where the profiles can then be compared with, or replaced by, convex envelopes.
--
--   **Formalization Note** The conclusion is `EnvelopeBounds (negativeLog w) (positiveLog w) b c`, with $P_w$ = `negativeLog w` and $Q_w$ = `positiveLog w`. No convexity or growth of $w$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean#L237-L250

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.bounds_of_weight {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) {b c : ℤ → ℂ}
    (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖ * w j ≤ 1) :
    EnvelopeBounds (negativeLog w) (positiveLog w) b c := by sorry
