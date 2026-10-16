-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_Computation_qGuardInv_error
-- name    : OAI.BoxTransport.Routing.Computation.qGuardInv_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:23:23.601032+00:00
-- url     : https://prove2.me/theorems/1848e0c6-ed9f-49e1-a9e2-01559ab7ae98
-- title:
--   Error bound for the guarded rational reciprocal
-- statement:
--   A triple $q=(p,r,d)\in\mathbb{N}^3$ codes the rational number $\operatorname{val}(q)=(p-r)/(d+1)$; reciprocals, absolute values and comparisons of codes are computed exactly. For $b\in\mathbb{N}$ the guarded reciprocal $G_b(q)$ is a code of $1/\operatorname{val}(q)$ if $|\operatorname{val}(q)|\ge1/(2(b+1))$, and the code of $0$ otherwise.
--
--   **Theorem.** Let $b\in\mathbb{N}$, let $q$ be a code and let $x\in\mathbb{R}$ with $|x|\ge1/(b+1)$. Then
--
--   $$\Big|\frac{1}{x}-\operatorname{val}\big(G_b(q)\big)\Big|\le2(b+1)^2\,\big|x-\operatorname{val}(q)\big|.$$
--
--   Inverting an approximate value is unstable near $0$; the guard replaces approximations that are too small by $0$. If the true value $x$ is known to stay at distance at least $1/(b+1)$ from $0$, the guarded reciprocal of an arbitrary rational approximation of $x$ approximates $1/x$ with error amplification at most $2(b+1)^2$; no assumption on the quality of the approximation is needed. This is the reciprocal step in the exact-rational evaluation of smooth expressions.
--
--   **Formalization Note** $G_b(q)$ is `qGuardInv b q`, defined by the decidable comparison `qLe (qInv (qNat (2 * (b + 1)))) (qAbs q)`; codes are `QCode` with value `Qval`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Expressions.lean#L218-L263

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions

open OAI OAI.BoxTransport OAI.BoxTransport.Routing OAI.BoxTransport.Routing.Computation
open scoped Topology
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec

theorem OAI.BoxTransport.Routing.Computation.qGuardInv_error (b : ℕ) (q : QCode) {x : ℝ}
    (hx : ((b : ℝ) + 1)⁻¹ ≤ |x|) :
    |x⁻¹ - (Qval (qGuardInv b q) : ℝ)| ≤ 2 * ((b : ℝ) + 1) ^ 2 * |x - (Qval q : ℝ)| := by sorry
