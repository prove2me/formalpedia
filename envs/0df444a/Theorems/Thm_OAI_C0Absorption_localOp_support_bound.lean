-- Prove2me | Theorems.Thm_OAI_C0Absorption_localOp_support_bound
-- name    : OAI.C0Absorption.localOp_support_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:03:00.041486+00:00
-- url     : https://prove2.me/theorems/c182ddcc-840e-42a1-8d2d-e85ea3d9eaa8
-- title:
--   Support control for flattening and remainder operators
-- statement:
--   For a centre $q$ and a radius $\varepsilon>0$, the flattening $G_{q,\varepsilon}u=u(q)+\chi(d(\cdot,q)/\varepsilon)(u-u(q))$ freezes $u$ near $q$, and the remainder is $R_{q,\varepsilon}u=G_{q,\varepsilon}u-u$; $\chi(t)=\min(1,\max(0,2t-1))$. Let $v$ be $K$-Lipschitz and suppose $v\le a$ on the closed support of $u$. Then for both the flattening and the remainder operator $T\in\{G_{q,\varepsilon},R_{q,\varepsilon}\}$,
--   $$
--   v(x)\le a+\varepsilon K\qquad\text{for all }x\in\operatorname{supp}(Tu).
--   $$
--
--   The operators enlarge supports by at most the radius $\varepsilon$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Localization.lean#L431-L445

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology

theorem OAI.C0Absorption.localOp_support_bound {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u v : X → ℝ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (a : ℝ) (ha : ∀ x ∈ tsupport u, v x ≤ a) :
    ∀ x ∈ tsupport (localOp isG q ε u), v x ≤ a+ε*K := by sorry
