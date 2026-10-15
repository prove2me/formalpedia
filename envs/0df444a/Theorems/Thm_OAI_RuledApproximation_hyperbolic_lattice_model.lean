-- Prove2me | Theorems.Thm_OAI_RuledApproximation_hyperbolic_lattice_model
-- name    : OAI.RuledApproximation.hyperbolic_lattice_model
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:47:19.881316+00:00
-- url     : https://prove2.me/theorems/643ecbfc-eaa3-4e9a-98d7-ea2788c94313
-- title:
--   The hyperbolic linear map $(x_1,x_2)\mapsto\lambda\,(x_2,x_1)$ admits a lattice model
-- statement:
--   Equip $\mathbb{R}^2$ with the maximum norm, let $\Lambda_n=\tfrac1n\mathbb{Z}^2$, and let $J(x_1,x_2)=(x_2,x_1)$ be the coordinate swap. For a linear map $A$ of $\mathbb{R}^2$ and real numbers $L,R$, say that $(A,L,R)$ is a *lattice model* if for every integer $n\ge1$, every $p\in\mathbb{R}^2$ and every $r$ with $|r|\le L$ there is $b\in\Lambda_n$ with $\|b-p\|_\infty\le R/n$ and $\|(p-b)+rA(p-b)\|_\infty\le\frac1{2n}$.
--
--   Let $L,\lambda$ be real numbers with $L>0$ and $0<L\lambda<1$. Then $\bigl(\lambda J,\ L,\ \tfrac{1}{2(1-L\lambda)}\bigr)$ is a lattice model: for every integer $n\ge1$, every $p\in\mathbb{R}^2$ and every $r$ with $|r|\le L$ there is $b\in\Lambda_n$ with
--   $$
--   \|b-p\|_\infty\le\frac{1}{2(1-L\lambda)\,n}\qquad\text{and}\qquad\|(p-b)+r\lambda J(p-b)\|_\infty\le\frac1{2n}.
--   $$
--
--   The map $\lambda J$ has eigenvalues $\lambda$ and $-\lambda$, and for $\lambda>0$ it is the normal form, in suitable linear coordinates, of every linear map of the plane with eigenvalues $\lambda$ and $-\lambda$. This result therefore supplies the lattice-model hypothesis of the local covering construction at hyperbolic points.
--
--   **Formalization Note** The map is `lam • swapCLM` on `Parameter` (the type `Fin 2 → ℝ`), and the conclusion is `LatticeModel (lam • swapCLM) L (1 / (2 * (1 - L * lam)))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/HyperbolicLattice.lean#L28-L82

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.hyperbolic_lattice_model {L lam : ℝ} (hL : 0 < L)
    (hlam : 0 < L * lam) (hsmall : L * lam < 1) :
    LatticeModel (lam • swapCLM) L (1 / (2 * (1 - L * lam))) := by sorry
