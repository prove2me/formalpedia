-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_bilateralWeight_ratio
-- name    : OAI.BackwardIntertwiners.bilateralWeight_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:30:26.337981+00:00
-- url     : https://prove2.me/theorems/874917db-71fb-43e3-89bd-445d6dc25373
-- title:
--   Step ratios of the explicit bilateral weight are the shift weights $e^{-\varepsilon(j)}$
-- statement:
--   Let $t,u:\mathbb{N}\to\mathbb{N}$ be arbitrary. For $s\in\{t,u\}$ and $k,n\in\mathbb{N}$ define, with $\kappa(k)=\lfloor\log_8k\rfloor+1$ for $k\ge1$,
--   $$\rho_s(0)=0,\quad \rho_s(k)=100\bigl(2^{\kappa(k)}-2+s(\kappa(k))\bigr)\ (k\ge1),\quad e_s(k)=10(k+1)+\rho_s(k),\quad S_s(n)=\sum_{k=0}^{n-1}e_s(k).$$
--   The **bilateral weight** $\omega=\omega_{t,u}:\mathbb{Z}\to\mathbb{R}$, the **bilateral exponent** $\varepsilon=\varepsilon_{t,u}:\mathbb{Z}\to\mathbb{R}$ and the **shift weights** $\beta=\beta_{t,u}:\mathbb{Z}\to\mathbb{R}$ are defined, for $n\in\mathbb{N}$ and $j\in\mathbb{Z}$, by
--   $$\omega(n)=e^{-S_t(n)},\quad \omega(-n-1)=e^{S_u(n+1)},\qquad \varepsilon(n)=e_t(n),\quad \varepsilon(-n-1)=e_u(n),\qquad \beta(j)=e^{-\varepsilon(j)}.$$
--   So the right half of $\omega$ is governed by $t$ and the left half by $u$.
--
--   **Theorem.** For every $j\in\mathbb{Z}$,
--   $$\frac{\omega(j+1)}{\omega(j)}=\beta(j).$$
--
--   No condition on $t$ and $u$ is needed. The identity says that $\omega$ is the weight sequence of the bilateral weighted shift with weights $\beta$: on $\ell^2(\mathbb{Z})$ the shift $(Tv)_j=\beta(j-1)\,v_{j-1}$ can be written as $(Tv)_j=\frac{\omega(j)}{\omega(j-1)}\,v_{j-1}$, so that $(T^rv)_j=\frac{\omega(j)}{\omega(j-r)}\,v_{j-r}$. This is how the explicit forward shifts of the construction are matched with the abstract weighted-shift results, and it also drives the commutation relation between the forward and backward fibered shifts.
--
--   **Formalization Note** `bilateralWeight t u`, `bilateralExponent t u` and `bilateralBeta t u` are defined by pattern matching on `Int.ofNat n` and `Int.negSucc n`, that is, on $n$ and $-n-1$. Since $\omega>0$, the division is an honest division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean#L197-L214

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.bilateralWeight_ratio (t u : ℕ → ℕ) (j : ℤ) :
    bilateralWeight t u (j+1) / bilateralWeight t u j = bilateralBeta t u j := by sorry
