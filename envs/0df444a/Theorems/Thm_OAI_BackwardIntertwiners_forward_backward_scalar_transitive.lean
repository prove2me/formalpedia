-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_forward_backward_scalar_transitive
-- name    : OAI.BackwardIntertwiners.forward_backward_scalar_transitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:35:53.525627+00:00
-- url     : https://prove2.me/theorems/a9c86e27-4291-4cb0-a93c-4b90a44e66de
-- title:
--   No nontrivial closed subspace is invariant under the forward shift, the backward shift and all multipliers
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
--   *Multipliers.* For a bounded measurable function $g\in L^\infty(\mathbb{Z}_2,\mu;\mathbb{C})$ let $M_g$ be the multiplication operator $(M_gf)(x)=g(x)\,f(x)$ on $\mathcal H$.
--
--   **Theorem.** Let $L\subseteq\mathcal H$ be a closed complex linear subspace such that $S(L)\subseteq L$, $V(L)\subseteq L$, and $M_g(L)\subseteq L$ for every $g\in L^\infty(\mathbb{Z}_2,\mu;\mathbb{C})$. Then
--   $$L=\{0\}\qquad\text{or}\qquad L=\mathcal H .$$
--
--   The operator $S$ commutes with $V$ and with every $M_g$, so any closed subspace invariant under the whole commutant of $S$ satisfies the hypotheses. The theorem is therefore the key step in showing that the commutant of the quasinilpotent operator $S$ is transitive, that is, has no closed invariant subspace other than $\{0\}$ and $\mathcal H$. It combines the support separation theorem for quadratic weights in each fiber with the ergodicity of the odometer $x\mapsto x+1$ on $\mathbb{Z}_2$.
--
--   **Formalization Note** $L$ is a `Submodule ℂ GlobalHilbert` with `IsClosed (L : Set GlobalHilbert)`; invariance is `OperatorInvariant L T`, i.e. `∀ v ∈ L, T v ∈ L`; $M_g$ is `scalarMultiplier g` for `g : Lp ℂ ∞ baseMeasure`; and $\{0\}$, $\mathcal H$ are `⊥`, `⊤`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ErgodicTransitivity.lean#L203-L239

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
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
open Topology MeasureTheory Set
open scoped ENNReal

theorem OAI.BackwardIntertwiners.forward_backward_scalar_transitive (L : Submodule ℂ GlobalHilbert)
    (hclosed : IsClosed (L : Set GlobalHilbert))
    (hS : OperatorInvariant L forwardOperator)
    (hV : OperatorInvariant L backwardOperator)
    (hM : ∀ g : Lp ℂ ∞ baseMeasure, OperatorInvariant L (scalarMultiplier g)) :
    L = ⊥ ∨ L = ⊤ := by sorry
