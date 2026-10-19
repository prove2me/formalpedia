-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Weighted_weighted_terminal
-- name    : OAI.SubsphereCurrent.Weighted.weighted_terminal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:01:41.338203+00:00
-- url     : https://prove2.me/theorems/b9b76ebd-5f92-4150-9193-40f4f9120608
-- title:
--   The radius-weighted norm of a terminal success function is at most $16^d\varepsilon^{d/16}$
-- statement:
--   Let $d,n\in\mathbb N$ and let $S^{d-1}$ be the unit sphere of $\mathbb R^d$. An *affine test* $A$ of dimension $n$ consists of a linear subspace $H_A\subseteq\mathbb R^d$ with $\dim H_A=n$, a center $c_A\in H_A^\perp$ and a radius $r_A>0$ with $\|c_A\|^2+r_A^2=1$; then $c_A+r_As\in S^{d-1}$ for every $s$ in the unit sphere $S_{H_A}$ of $H_A$. Write $\sigma_H$ for the uniform (normalized surface) measure on the unit sphere $S_H$ of a subspace $H$. For $g:S^{d-1}\to[0,\infty]$ the *radius-weighted norm at level $n$* is
--   $$\|g\|_{d,n}=\sup_{A}\ r_A^{\,d/16}\int_{S_{H_A}}g\big(c_A+r_As\big)\,d\sigma_{H_A}(s),$$
--   the supremum running over all affine tests of dimension $n$. For a probability measure $\pi$ on $S^{d-1}$ and $\varepsilon\in\mathbb R$, the *terminal input* $\tau_{\pi,\varepsilon}(s)=\pi\big\{u\in S^{d-1}:\arccos\langle u,s\rangle\le\varepsilon\big\}$ ($s\in S^{d-1}$) is the probability that an output drawn from $\pi$ is within angle $\varepsilon$ of $s$.
--
--   **Theorem.** Let $d\ge4$, let $n$ be a natural number with $d/2\le n\le d$, let $\pi$ be a probability measure on $S^{d-1}$, and let $\varepsilon>0$. Then
--
--   $$
--   \|\tau_{\pi,\varepsilon}\|_{d,n}\;\le\;16^{d}\,\varepsilon^{d/16}.
--   $$
--
--   Thus a fixed output distribution, viewed through any affine slice of dimension $n\ge d/2$ and weighted by the slice radius, has success of order $\varepsilon^{d/16}$. This is the terminal estimate of the radius-weighted framework: it bounds the contribution of a learner's final output in the radius-weighted full estimate, with the explicit constant $C=16$, and complements the block estimate, which controls how the norm propagates through a block of observations.
--
--   **Formalization Note** The exponent $d/16$ is the real number $d/16$, and the comparison $d/2\le n$ is between real numbers. The norm is `Weighted.norm d n`, a supremum in $[0,\infty]$ over the structure `Affine.Test d n`, and the terminal input is `terminalInput π ε`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/Weighted.lean#L168-L213

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
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Weighted
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

theorem OAI.SubsphereCurrent.Weighted.weighted_terminal {d n : ℕ} (hd : 4 ≤ d) (hn : (d : ℝ)/2 ≤ n) (hnd : n ≤ d)
    (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    {ε : ℝ} (hε : 0 < ε) :
    norm d n (terminalInput π ε) ≤
      ENNReal.ofReal ((16 : ℝ)^d)*(ENNReal.ofReal ε)^((d : ℝ)/16) := by sorry
