-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_Computation_flatTerm_bound
-- name    : OAI.BoxTransport.Routing.Computation.flatTerm_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:20:17.074983+00:00
-- url     : https://prove2.me/theorems/5e22ece0-04d7-4af9-a38d-e80290c04417
-- title:
--   The flat functions $x^{-m}e^{-1/x}$ are bounded by $m!$
-- statement:
--   For $m\in\mathbb{N}$ let $\phi_m:\mathbb{R}\to\mathbb{R}$ be the flat function
--
--   $$\phi_m(x)=x^{-m}e^{-1/x}\quad(x>0),\qquad \phi_m(x)=0\quad(x\le0).$$
--
--   **Theorem.** For every $m\in\mathbb{N}$ and every $x\in\mathbb{R}$,
--
--   $$|\phi_m(x)|\le m!\,.$$
--
--   The functions $\phi_m$ are the building blocks of smooth cutoff functions ($\phi_0$ is the classical flat function $e^{-1/x}$ extended by $0$), and the family is closed under differentiation up to linear combinations, $\phi_m'=\phi_{m+2}-m\,\phi_{m+1}$. The explicit bound $m!$ makes them usable in effective error estimates: it bounds the values of flat-function nodes in expression trees and, through the derivative formula, yields explicit Lipschitz constants.
--
--   **Formalization Note** $\phi_m$ is `flatTerm m`, defined as the $m$-th power of the inverse of $x$ times Mathlib's `expNegInvGlue x`; for $x\le0$ the second factor is $0$, so Lean's convention $0^{-1}=0$ plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Computation.lean#L347-L363

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

theorem OAI.BoxTransport.Routing.Computation.flatTerm_bound (m : ℕ) (x : ℝ) : |flatTerm m x| ≤ (m.factorial : ℝ) := by sorry
