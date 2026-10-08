-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_theorem_3_2_ghs
-- name    : IsingLTL.FreeEntropy.theorem_3_2_ghs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:08.299029+00:00
-- url     : https://prove2.me/theorems/a2995fea-4a20-4d32-94af-d1df9e6a3a84
-- title:
--   Theorem 3.2 — GHS inequality: $\partial^2 m_j/\partial B_k\partial B_l\le0$
-- statement:
--   Let $\beta\ge0$ and, for fields $\underline B=\{B_i:i\in V\}$ on a finite graph, let $m_j(\underline B)=\mu(x_j=+1)-\mu(x_j=-1)$ be the local magnetization at $j$ in the Ising model (3.1). If $B_i\ge0$ for all $i\in V$, then for any three vertices $j,k,l$ (not necessarily distinct)
--   $$\frac{\partial^2 m_j(\underline B)}{\partial B_k\,\partial B_l}\le0.$$
--
--   The Griffiths–Hurst–Sherman inequality says that magnetizations are concave in nonnegative fields.
--
--   **Formalization Note** The partial derivatives are directional derivatives in the field coordinates; $\underline B\mapsto m_j(\underline B)$ is a ratio of finite sums of exponentials, hence smooth.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 9, Theorem 3.2, (3.2) (cited from Griffiths, Hurst, Sherman 1970)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_IsingModel

namespace IsingLTL.FreeEntropy

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

end IsingLTL.FreeEntropy
