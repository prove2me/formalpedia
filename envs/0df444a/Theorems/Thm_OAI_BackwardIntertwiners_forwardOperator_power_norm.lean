-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_forwardOperator_power_norm
-- name    : OAI.BackwardIntertwiners.forwardOperator_power_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:34:48.51005+00:00
-- url     : https://prove2.me/theorems/66c31e67-9f99-4946-a749-9154ffbbb27d
-- title:
--   Norm bound $\|S^n\|\le e^{-10\lfloor (n+1)^2/4\rfloor}$ for powers of the forward fibered weighted shift
-- statement:
--   Let $\mathbb{Z}_2$ be the ring of 2-adic integers with its normalized Haar probability measure $\mu$ (completed), and let $\mathcal H=L^2(\mathbb{Z}_2,\mu;\ell^2(\mathbb{Z}))$ be the complex Hilbert space of (classes of) square-integrable functions $f$ from $\mathbb{Z}_2$ to $\ell^2(\mathbb{Z})$; write $f(x)_j$ for the $j$-th coordinate of $f(x)$.
--
--   *Explicit weights.* For $x\in\mathbb{Z}_2$ and $m\in\mathbb{N}$ let $r_m(x)\in\{0,\dots,2^m-1\}$ be the residue of $x$ modulo $2^m$, and put $t_x(m)=r_m(x)$ and $u_x(m)=2^m-1-r_m(x)$. For $s:\mathbb{N}\to\mathbb{N}$ let $\kappa(k)=\lfloor\log_8k\rfloor+1$ for $k\ge1$, $\rho_s(0)=0$, $\rho_s(k)=100\bigl(2^{\kappa(k)}-2+s(\kappa(k))\bigr)$ for $k\ge1$, $e_s(k)=10(k+1)+\rho_s(k)$ and $S_s(n)=\sum_{k=0}^{n-1}e_s(k)$. The fiber weight $\omega_x:\mathbb{Z}\to(0,\infty)$ and the shift weights $\beta_x:\mathbb{Z}\to(0,e^{-10}]$ are given, for $n\in\mathbb{N}$, by
--   $$\omega_x(n)=e^{-S_{t_x}(n)},\quad \omega_x(-n-1)=e^{S_{u_x}(n+1)},\qquad \beta_x(n)=e^{-e_{t_x}(n)},\quad \beta_x(-n-1)=e^{-e_{u_x}(n)}.$$
--
--   *Forward operator.* $S:\mathcal H\to\mathcal H$ acts fiberwise by a bilateral weighted forward shift: $(Sf)(x)=S_x\,f(x)$, where $(S_xv)_j=\beta_x(j-1)\,v_{j-1}$ for $v\in\ell^2(\mathbb{Z})$.
--
--   **Theorem.** For every $n\in\mathbb{N}$, the operator norm of the $n$-th power of $S$ on $\mathcal H$ satisfies
--   $$\|S^n\|\le\exp\Bigl(-10\Bigl\lfloor\frac{(n+1)^2}{4}\Bigr\rfloor\Bigr).$$
--
--   Since $10\lfloor(n+1)^2/4\rfloor\ge n^2$ for $n\ge2$, it follows that $\|S^n\|^{1/n}\le e^{-n}$ for $n\ge2$, so $\|S^n\|^{1/n}\to0$: the operator $S$ is quasinilpotent. This is the quasinilpotence part of the construction of an operator with transitive commutant.
--
--   **Formalization Note** $S$ is `forwardOperator` on `GlobalHilbert = Lp Fiber 2 baseMeasure`, $S^n$ is the $n$-th power in the algebra of continuous linear maps (so $S^0$ is the identity), and $\lfloor(n+1)^2/4\rfloor$ is `powerCost n`, computed by natural-number division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/GlobalOperators.lean#L454-L467

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
open Topology MeasureTheory Set
open scoped ENNReal

theorem OAI.BackwardIntertwiners.forwardOperator_power_norm (n : ℕ) :
    ‖forwardOperator^n‖ ≤ Real.exp (-10*(powerCost n:ℝ)) := by sorry
