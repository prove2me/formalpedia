-- Prove2me | Theorems.Thm_NesterovRCD_Constrained_eq_4_3
-- name    : NesterovRCD.Constrained.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:17.513492+00:00
-- url     : https://prove2.me/theorems/ed01e5e8-e311-4832-87a1-9cd681a1a08b
-- title:
--   (4.3) — the optimality condition of the block subproblem (4.2)
-- statement:
--   Consider the constrained problem (4.1): $Q=Q_1\times\cdots\times Q_n$ with each $Q_i\subseteq\mathbb R^{n_i}$ nonempty, closed and convex, each $\mathbb R^{n_i}$ carrying a Euclidean norm $\|h\|_{(i)}^2=\langle B_ih,h\rangle$ (3.4), and $f:\mathbb R^N\to\mathbb R$ convex with coordinate-wise Lipschitz gradient (2.2), constants $L_i>0$. For $x\in\mathbb R^N$ and a block $i$, let $u^{(i)}(x)$ be the solution of the block subproblem (4.2),
--   $$u^{(i)}(x)=\arg\min_{u\in Q_i}\Big[\langle f'_i(x),u-x^{(i)}\rangle+\tfrac{L_i}2\|u-x^{(i)}\|_{(i)}^2\Big].$$
--   Then $u^{(i)}(x)\in Q_i$ and
--   $$\big\langle f'_i(x)+L_iB_i\big(u^{(i)}(x)-x^{(i)}\big),\,u-u^{(i)}(x)\big\rangle\ge0\qquad\text{for all }u\in Q_i .$$
--
--   This variational inequality is the only property of the update used in the rest of §4: with $u=x^{(i)}$ it gives the decrease (4.4), and with $u=x_*^{(i)}$ it gives the Lyapunov inequality (4.7).
--
--   **Formalization Note** The paper writes $u^i$ for the bound variable $u^{(i)}$ (a typo). The Euclidean block norm is an inner product space structure on $E_i$, whose inner product is the paper's $\langle B_i\cdot,\cdot\rangle$; the pairing $\langle f'_i(x),h\rangle$ is the functional $f'_i(x)$ applied to $h$. The conclusion includes $u^{(i)}(x)\in Q_i$, i.e. that the subproblem has a solution, which the paper takes for granted in (4.2); the Lean update is a `Classical.epsilon` choice among solutions. The standing assumptions of §4 ($f$ convex, (2.2), $Q_i$ closed and convex) are stated, together with $Q_i\ne\emptyset$, which the paper leaves implicit, and $n\ge1$. Indices are `Fin n`, 0-based.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 13, §4, (4.3)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM

namespace NesterovRCD.Constrained

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem eq_4_3 (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) (x : NesterovRCD.Sublinear.Blocks E) (i : Fin n) :
    blockUpdate f L Q x i ∈ Q i ∧
      ∀ w ∈ Q i, 0 ≤ NesterovRCD.Sublinear.partialGrad f x i (w - blockUpdate f L Q x i)
        + L i * inner ℝ (blockUpdate f L Q x i - x i) (w - blockUpdate f L Q x i) := by sorry

end NesterovRCD.Constrained
