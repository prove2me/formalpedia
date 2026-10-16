-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_Computation_evalE_error
-- name    : OAI.BoxTransport.Routing.Computation.evalE_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:26:15.708989+00:00
-- url     : https://prove2.me/theorems/61d7781e-3435-46d2-9f36-74de8c7dc3a7
-- title:
--   Error propagation bound for exact-rational evaluation of smooth expressions
-- statement:
--   **Codes and expressions.** A triple $(p,r,d)\in\mathbb{N}^3$ codes the rational number $\operatorname{val}(p,r,d)=(p-r)/(d+1)$, and $q_\mu$ denotes the code numbered $\mu$ under a fixed enumeration of $\mathbb{N}^3$. For $\mu\in\mathbb{N}$ let $\phi_\mu(y)=y^{-\mu}e^{-1/y}$ for $y>0$, $\phi_\mu(y)=0$ for $y\le0$, and $L_\mu=(\mu+2)!+\mu\,(\mu+1)!$. Expressions are finite trees built from leaves $T,X_1,X_2,X_3$, sums, products, negations, and unary nodes: rational constants $q_\mu$, reciprocals $1/e$ with a guard $\mu$, and flat functions $\phi_\mu(e)$. The value $e(t,x)$ reads the leaves as $t,x_1,x_2,x_3$. An expression is *valid* if below every reciprocal node with guard $\mu$ the subexpression $e$ satisfies $|e(t,x)|\ge1/(\mu+1)$ everywhere. For $R\in\mathbb{N}$ the value bound $B_R(e)$ is defined by $B_R=R$ on leaves, $B_R(e+f)=B_R(e)+B_R(f)$, $B_R(e\cdot f)=B_R(e)B_R(f)$, $B_R(-e)=B_R(e)$, $B_R=p+r$ for a constant with code $(p,r,d)$, $B_R=\mu+1$ for a reciprocal with guard $\mu$, and $B_R=\mu!$ for $\phi_\mu$.
--
--   **Rational evaluation.** A rational point code is a quadruple $q=(q_0,q_1,q_2,q_3)$ of codes; it denotes the point $P(q)=(\operatorname{val}q_0,\operatorname{val}q_1,\operatorname{val}q_2,\operatorname{val}q_3)\in\mathbb{R}\times\mathbb{R}^3$. For $N\in\mathbb{N}$ the evaluation $E_N(e)$ is the code defined recursively by: the leaves return $q_0,q_1,q_2,q_3$; sums, products and negations are computed by exact code arithmetic; a constant returns its code; a reciprocal with guard $\mu$ whose child evaluates to $w$ returns a code of $1/\operatorname{val}(w)$ if $|\operatorname{val}(w)|\ge1/(2(\mu+1))$ and the code of $0$ otherwise; and $\phi_\mu$ applied to a child evaluating to $w$ returns the code of $0$ if $z=\operatorname{val}(w)\le0$, and otherwise the code of $z^{-\mu}\sum_{k<n}(-1/z)^k/k!$, where $n$ is the least natural number with $n+1\ge2/z$ and $2z^{-n}/n!\le1/((N+1)(\beta+1)+1)$, $\beta=p'+r'$ being read off the code $(p',r',d')$ of $z^{-\mu}$ produced by exact code arithmetic.
--
--   **Amplification.** Define $A_R(e)\in\mathbb{N}$ by $A_R=0$ on leaves and constants, $A_R(e+f)=A_R(e)+A_R(f)$, $A_R(e\cdot f)=\big(B_R(e)+A_R(e)\big)A_R(f)+B_R(f)A_R(e)$, $A_R(-e)=A_R(e)$, $A_R(1/e)=2(\mu+1)^2A_R(e)$ for guard $\mu$, and $A_R(\phi_\mu(e))=L_\mu A_R(e)+1$.
--
--   **Theorem.** Let $e$ be a valid expression, $q$ a rational point code and $N,R\in\mathbb{N}$ with $\|P(q)\|=\max(|t|,|x_1|,|x_2|,|x_3|)\le R$, where $P(q)=(t,x)$. Then
--
--   $$\big|e(P(q))-\operatorname{val}\big(E_N(e)\big)\big|\le\frac{A_R(e)}{N+1}.$$
--
--   The error of the exact-rational evaluation is thus controlled by an amplification factor read off the syntax of $e$. Taking $N$ proportional to $A_R(e)$ yields any prescribed precision, which is how values of representable functions, and after symbolic differentiation all their mixed partial derivatives, are approximated to arbitrary accuracy at rational points.
--
--   **Formalization Note** Expressions are `Expr := Nat.Partrec.Code` (constructors `zero`, `succ`, `left`, `right`, `pair`, `comp`, `rfind'`, `prec`, with the unary operation selected by `Encodable.encode m` modulo $3$). $E_N$ is `evalE q N`, $A_R$ is `ampE R`, $B_R$ is `boundE R`, $P(q)$ is `codeSpaceTime q`, the reciprocal step is `qGuardInv` and the flat step is `qFlat`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Expressions.lean#L355-L405

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

theorem OAI.BoxTransport.Routing.Computation.evalE_error {e : Expr} (he : Valid e) (q : RationalPointCode) (N R : ℕ)
    (hR : ‖codeSpaceTime q‖ ≤ R) :
    |value e (codeSpaceTime q) - (Qval (evalE q N e) : ℝ)| ≤
      (ampE R e : ℝ) * ((N : ℝ) + 1)⁻¹ := by sorry
