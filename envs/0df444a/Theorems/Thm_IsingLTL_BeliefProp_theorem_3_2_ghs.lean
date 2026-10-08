-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_theorem_3_2_ghs
-- name    : IsingLTL.BeliefProp.theorem_3_2_ghs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:24.781998+00:00
-- url     : https://prove2.me/theorems/99492df2-ee5f-454a-a249-8fd988748114
-- title:
--   The GHS inequality (Theorem 3.2)
-- statement:
--   Let $G=(V,E)$ be a finite graph, $\beta\ge0$, and for a field vector $\underline B=\{B_i:i\in V\}$ let
--   $$m_j(\underline B)=\mu(x_j=+1)-\mu(x_j=-1)$$
--   be the local magnetization at vertex $j$ in the Ising model (3.1). If $B_i\ge0$ for all $i\in V$, then for any three vertices $j,k,l\in V$ (not necessarily distinct),
--   $$\frac{\partial^2 m_j(\underline B)}{\partial B_k\,\partial B_l}\le 0.$$
--
--   The GHS (Griffiths–Hurst–Sherman) inequality says that magnetizations are concave in the nonnegative fields; the paper uses it to compare the effect of boundary fields at different depths of a tree.
--
--   **Formalization Note** The partial derivatives are directional derivatives along the coordinate vectors; $\underline B\mapsto m_j(\underline B)$ is smooth (a ratio of finite sums of exponentials).
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 9, Theorem 3.2, eq. (3.2) (citing Griffiths, Hurst, Sherman 1970)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_IsingModel

namespace IsingLTL.BeliefProp

/-- **Theorem 3.2 (Griffiths, Hurst, Sherman)** (Dembo–Montanari, arXiv:0804.4726v3, p. 9). Let
`β ≥ 0` and let `m_j(B) = μ(x_j = +1) − μ(x_j = −1)` be the local magnetization at `j` in the
Ising model (3.1) with fields `B = {B_i}`. If `B_i ≥ 0` for all `i`, then for any three vertices
`j, k, l` (not necessarily distinct), `∂²m_j(B)/∂B_k ∂B_l ≤ 0` (3.2).

Formalization Note: `V` is finite. `partialDeriv k F B = d/dt F(B + t e_k)|_{t=0}`; the map
`B ↦ m_j(B)` is a ratio of finite sums of exponentials, hence smooth, so the iterated directional
derivative is the mixed partial derivative of (3.2). -/
theorem theorem_3_2_ghs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (hβ : 0 ≤ β)
    (B : V → ℝ) (hB : ∀ i, 0 ≤ B i) (j k l : V) :
    partialDeriv l (partialDeriv k (localMag G β j)) B ≤ 0 := by sorry

end IsingLTL.BeliefProp
