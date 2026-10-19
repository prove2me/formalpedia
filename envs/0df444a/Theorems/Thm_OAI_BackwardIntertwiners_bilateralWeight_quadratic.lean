-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_bilateralWeight_quadratic
-- name    : OAI.BackwardIntertwiners.bilateralWeight_quadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:31:40.865978+00:00
-- url     : https://prove2.me/theorems/3485ee05-95f6-4893-9128-3659e0f31acf
-- title:
--   Explicit bilateral weights built from residue data are quadratic weights
-- statement:
--   Let $t,u:\mathbb{N}\to\mathbb{N}$ satisfy $t(m)<2^m$ and $u(m)<2^m$ for every $m\in\mathbb{N}$. For $s\in\{t,u\}$ define, with $\kappa(k)=\lfloor\log_8k\rfloor+1$ for $k\ge1$,
--   $$\rho_s(0)=0,\quad \rho_s(k)=100\bigl(2^{\kappa(k)}-2+s(\kappa(k))\bigr)\ (k\ge1),\quad e_s(k)=10(k+1)+\rho_s(k),\quad S_s(n)=\sum_{k=0}^{n-1}e_s(k),$$
--   and let $\omega=\omega_{t,u}:\mathbb{Z}\to\mathbb{R}$ be the bilateral weight given by $\omega(n)=e^{-S_t(n)}$ and $\omega(-n-1)=e^{S_u(n+1)}$ for $n\in\mathbb{N}$.
--
--   Call a function $F:\mathbb{N}\to\mathbb{R}$ discretely convex if $F(n+1)-F(n)$ is nondecreasing in $n$, and call $w:\mathbb{Z}\to\mathbb{R}$ a **quadratic weight** if (1) $w(j)>0$ for all $j$; (2) $w$ is nonincreasing on $\mathbb{Z}$; (3) $n\mapsto\log w(-n)$ is discretely convex; (4) $n\mapsto-\log w(n)$ is discretely convex; (5) the family $\bigl(w(j)^{1/j}\bigr)_{j\in\mathbb{Z},\,j\neq0}$ is summable; (6) there is a real number $a>\log3$ with
--   $$\lim_{n\to\infty}\frac{\log w(n)}{n^2}=-a\qquad\text{and}\qquad\lim_{n\to\infty}\frac{\log w(-n)}{n^2}=a .$$
--
--   **Theorem.** Under the hypotheses $t(m)<2^m$ and $u(m)<2^m$ for all $m$, the bilateral weight $\omega_{t,u}$ is a quadratic weight.
--
--   In the construction, $t$ and $u$ are the residues $x\bmod 2^m$ of a 2-adic integer $x$ and their complements $2^m-1-(x\bmod 2^m)$, so this theorem shows that every fiber weight of the forward weighted shift satisfies the hypotheses of the support separation theorem for quadratic weights.
--
--   **Formalization Note** The conclusion is `QuadraticWeights (bilateralWeight t u)` and the hypotheses are `ResidueBounds t` and `ResidueBounds u`. In condition (5), $w(j)^{1/j}$ is `Real.rpow` with exponent `1 / (j : ℝ)`, and the $j=0$ term is replaced by $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean#L269-L282

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

theorem OAI.BackwardIntertwiners.bilateralWeight_quadratic {t u : ℕ → ℕ} (ht : ResidueBounds t) (hu : ResidueBounds u) :
    QuadraticWeights (bilateralWeight t u) := by sorry
