-- Prove2me | Theorems.Thm_OAI_GAD_hasDerivAt_woottersSlope
-- name    : OAI.GAD.hasDerivAt_woottersSlope
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:23:52.341149+00:00
-- url     : https://prove2.me/theorems/31662980-a200-4c4a-a8dc-abcc01c0fc3c
-- title:
--   Derivative of the slope function $2s\,L(r)/r$ with $r=\sqrt{1-4s^2}$
-- statement:
--   For $0<s<\frac12$ put
--   $$r(s)=\sqrt{1-4s^2},\qquad L(t)=\log(1+t)-\log(1-t),\qquad W(s)=\frac{2s}{r(s)}\,L\bigl(r(s)\bigr),$$
--   with natural logarithms; on this interval $0<r(s)<1$. Then $W$ is differentiable at every $s\in(0,\frac12)$, and
--
--   $$
--   W'(s)=\frac{2\bigl(L(r(s))-2\,r(s)\bigr)}{r(s)^3}.
--   $$
--
--   The function $W$ is the derivative of $s\mapsto g(s^2)$ on $(0,\frac12)$, where $g(u)=h\bigl(\frac{1+\sqrt{1-4u}}2\bigr)$ and $h(p)=-p\log p-(1-p)\log(1-p)$ is the binary entropy. The formula above is therefore the second derivative of $s\mapsto g(s^2)$. Since $L(t)\ge2t$ for $0\le t<1$, it is nonnegative, which yields convexity of $s\mapsto g(s^2)$ on $[0,\frac12]$, an ingredient in the analysis of the single-qubit Holevo objective of the generalized amplitude-damping channel, in which $g$ appears.
--
--   **Formalization Note** $r$, $L$ and $W$ are `radius`, `logRatio` and `woottersSlope`; the conclusion is Mathlib's `HasDerivAt woottersSlope (...) s` under the hypothesis `s ∈ Ioo 0 (1/2)`. These functions are defined on all of $\mathbb{R}$ with Lean's total conventions, but only the open interval matters here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/OutputConvexity.lean#L102-L116

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity

open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators
open Set Filter Topology

theorem OAI.GAD.hasDerivAt_woottersSlope {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt woottersSlope
      (2 * (logRatio (radius s) - 2 * radius s) / radius s ^ 3) s := by sorry
