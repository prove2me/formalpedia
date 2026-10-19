-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_forward_backward_commute
-- name    : OAI.BackwardIntertwiners.forward_backward_commute
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:34:08.07922+00:00
-- url     : https://prove2.me/theorems/737675c9-1a4e-49f7-a9c8-4b67bfa45484
-- title:
--   The forward and backward fibered weighted shifts over the 2-adic odometer commute
-- statement:
--   Let $\mathbb{Z}_2$ be the ring of 2-adic integers with its normalized Haar probability measure $\mu$ (completed), and let $\mathcal H=L^2(\mathbb{Z}_2,\mu;\ell^2(\mathbb{Z}))$ be the complex Hilbert space of (classes of) square-integrable functions $f$ from $\mathbb{Z}_2$ to $\ell^2(\mathbb{Z})$; write $f(x)_j$ for the $j$-th coordinate of $f(x)$.
--
--   *Explicit weights.* For $x\in\mathbb{Z}_2$ and $m\in\mathbb{N}$ let $r_m(x)\in\{0,\dots,2^m-1\}$ be the residue of $x$ modulo $2^m$, and put $t_x(m)=r_m(x)$ and $u_x(m)=2^m-1-r_m(x)$. For $s:\mathbb{N}\to\mathbb{N}$ let $\kappa(k)=\lfloor\log_8k\rfloor+1$ for $k\ge1$, $\rho_s(0)=0$, $\rho_s(k)=100\bigl(2^{\kappa(k)}-2+s(\kappa(k))\bigr)$ for $k\ge1$, $e_s(k)=10(k+1)+\rho_s(k)$ and $S_s(n)=\sum_{k=0}^{n-1}e_s(k)$. The fiber weight $\omega_x:\mathbb{Z}\to(0,\infty)$ and the shift weights $\beta_x:\mathbb{Z}\to(0,e^{-10}]$ are given, for $n\in\mathbb{N}$, by
--   $$\omega_x(n)=e^{-S_{t_x}(n)},\quad \omega_x(-n-1)=e^{S_{u_x}(n+1)},\qquad \beta_x(n)=e^{-e_{t_x}(n)},\quad \beta_x(-n-1)=e^{-e_{u_x}(n)}.$$
--
--   *Forward operator.* $S:\mathcal H\to\mathcal H$ acts fiberwise by a bilateral weighted forward shift: $(Sf)(x)=S_x\,f(x)$, where $(S_xv)_j=\beta_x(j-1)\,v_{j-1}$ for $v\in\ell^2(\mathbb{Z})$.
--
--   *Backward operator.* For $y\in\mathbb{Z}_2$ and $j\in\mathbb{Z}$ put $\pi_y(j)=\dfrac{\omega_{y+1}(j-1)}{e^{10}\,\omega_y(j)}$. If $y$ is not an ordinary integer (that is, $y\notin\mathbb{Z}\subset\mathbb{Z}_2$), let $\gamma_y(j)=\pi_y(j)/\sup_{k\in\mathbb{Z}}\pi_y(k)$ (for such $y$ the supremum is finite and at least $\pi_y(0)=1$); if $y\in\mathbb{Z}$, let $\gamma_y(j)=0$. Thus $0\le\gamma_y(j)\le1$. Let $V_y$ be the backward weighted shift $(V_yv)_j=\gamma_y(j+1)\,v_{j+1}$ on $\ell^2(\mathbb{Z})$, and define $V:\mathcal H\to\mathcal H$ by
--   $$(Vf)(x)=V_{x-1}\,f(x-1),$$
--   that is, a backward weighted shift in the fiber combined with the translation $x\mapsto x-1$ of the base.
--
--   **Theorem.** The forward and backward operators commute:
--   $$SV=VS .$$
--
--   The operator $S$ is a direct integral of bilateral weighted shifts over $\mathbb{Z}_2$, and $V$ couples neighbouring fibers through the odometer $x\mapsto x+1$. The theorem places $V$ in the commutant of $S$. Together with the operators of multiplication by bounded scalar functions, which commute with $S$ because $S$ acts fiberwise, $V$ supplies the commuting operators used to prove that the commutant of $S$ has no nontrivial closed invariant subspace.
--
--   **Formalization Note** The base is the completion `Base` of `PadicInt 2` with respect to `baseHaar = addHaarMeasure ⊤`, the space is `GlobalHilbert = Lp Fiber 2 baseMeasure` with `Fiber = lp (fun _ : ℤ => ℂ) 2`, and the product `*` of continuous linear maps is composition. The functions $\omega_x$, $\beta_x$, $\pi_y$, $\gamma_y$ are `explicitWeight`, `explicitBeta`, `rawBackward`, `backwardCoeff`; the supremum is `⨆ k, rawBackward y k`, and the non-integer points form `goodBase`. `backwardOperator` is `backwardFieldOperator` followed by composition with the measure-preserving map `inverseOdometer x = x - 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/GlobalOperators.lean#L397-L409

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

theorem OAI.BackwardIntertwiners.forward_backward_commute : forwardOperator * backwardOperator = backwardOperator * forwardOperator := by sorry
