-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_Computation_flatTerm_lipschitz
-- name    : OAI.BoxTransport.Routing.Computation.flatTerm_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:21:23.20324+00:00
-- url     : https://prove2.me/theorems/1e62a24b-540a-49b7-865f-0c17cde125cc
-- title:
--   Lipschitz constant $(m+2)!+m\,(m+1)!$ for the flat function $x^{-m}e^{-1/x}$
-- statement:
--   For $m\in\mathbb{N}$ let $\phi_m(x)=x^{-m}e^{-1/x}$ for $x>0$ and $\phi_m(x)=0$ for $x\le0$, and put $L_m=(m+2)!+m\,(m+1)!\in\mathbb{N}$.
--
--   **Theorem.** $\phi_m$ is $L_m$-Lipschitz on $\mathbb{R}$:
--
--   $$|\phi_m(x)-\phi_m(y)|\le\big((m+2)!+m\,(m+1)!\big)\,|x-y|\qquad\text{for all } x,y\in\mathbb{R}.$$
--
--   The explicit constant controls how errors propagate through a flat function: if the argument is known up to an error $\delta$, then the value of $\phi_m$ is known up to $L_m\delta$. This is used when expressions containing flat functions are evaluated approximately in rational arithmetic.
--
--   **Formalization Note** $\phi_m$ is `flatTerm m` and $L_m$ is the natural number `flatLipschitzBound m`; the statement is Mathlib's `LipschitzWith`, with the constant cast to a nonnegative real.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Computation.lean#L367-L380

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation

open OAI OAI.BoxTransport OAI.BoxTransport.Routing OAI.BoxTransport.Routing.Computation
open scoped Topology
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.Computation.flatTerm_lipschitz (m : ℕ) : LipschitzWith (flatLipschitzBound m) (flatTerm m) := by sorry
