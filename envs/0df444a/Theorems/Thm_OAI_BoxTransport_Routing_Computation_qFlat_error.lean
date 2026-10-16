-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_Computation_qFlat_error
-- name    : OAI.BoxTransport.Routing.Computation.qFlat_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:22:21.024159+00:00
-- url     : https://prove2.me/theorems/1217f76e-59ad-4335-a72c-61cc6971fb82
-- title:
--   Rational approximation of $x^{-m}e^{-1/x}$ at rational points within $1/(N+1)$
-- statement:
--   **Rational codes.** A triple $q=(p,r,d)\in\mathbb{N}^3$ codes the rational number $\operatorname{val}(q)=(p-r)/(d+1)$. Sums, products, negations, reciprocals and powers of codes are computed by exact rational arithmetic on codes, and comparisons of codes compare their values. For a code $w=(p,r,d)$ put $\beta(w)=p+r\in\mathbb{N}$.
--
--   **Truncated exponential.** For a code $q$ and $N'\in\mathbb{N}$, let $x=\operatorname{val}(q)$ and let $n$ be the least natural number with $|x|/(n+1)\le1/2$ and $2|x|^n/n!\le1/(N'+1)$; then $E(q,N')$ is a code of the Taylor sum $\sum_{k<n}x^k/k!$.
--
--   **Flat approximation.** For $m,N\in\mathbb{N}$ and a code $q$ with $y=\operatorname{val}(q)$: if $y\le0$, then $F(m,q,N)$ is the code of $0$; if $y>0$, let $w$ be the code of $y^{-m}$ produced by exact code arithmetic and $q^-$ the code of $-1/y$, and let $F(m,q,N)$ be the code of $\operatorname{val}(w)\cdot\operatorname{val}\big(E(q^-,(N+1)(\beta(w)+1))\big)$.
--
--   Let $\phi_m(x)=x^{-m}e^{-1/x}$ for $x>0$ and $\phi_m(x)=0$ for $x\le0$.
--
--   **Theorem.** For all $m,N\in\mathbb{N}$ and every code $q$,
--
--   $$\big|\phi_m(\operatorname{val}(q))-\operatorname{val}(F(m,q,N))\big|\le\frac{1}{N+1}.$$
--
--   The map $(m,q,N)\mapsto F(m,q,N)$ involves only finitely many exact rational operations and an unbounded search with a decidable stopping rule, so it is a computable procedure producing rational approximations of the flat functions at rational points with any prescribed accuracy. It is the flat-function step in the exact-rational evaluation of smooth expressions, from which the effectivity of the routed velocity field is derived.
--
--   **Formalization Note** Codes have type `QCode` (triples of natural numbers) with value `Qval`; $F$ is `qFlat (m, q, N)`, $E$ is `qExp`, $\beta$ is `qBound`, and the test $y\le0$ is the decidable comparison `qLe q qZero`. The stopping index is obtained with `Nat.find`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Computation.lean#L421-L449

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
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.Computation.qFlat_error (m : ℕ) (q : QCode) (N : ℕ) :
    |flatTerm m (Qval q) - (Qval (qFlat (m, q, N)) : ℝ)| ≤ ((N : ℝ) + 1)⁻¹ := by sorry
