-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_theorem_2_6_bp_convergence
-- name    : IsingLTL.BeliefProp.theorem_2_6_bp_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:56.62232+00:00
-- url     : https://prove2.me/theorems/183d4682-be4b-4cec-b69c-aba3d33dcab4
-- title:
--   With a positive field, belief propagation converges exponentially fast from every positive initial condition (Theorem 2.6)
-- statement:
--   Let $\beta\ge0$, $B>0$ and $\Delta\in\mathbb N$. There exist $A=A(\beta,B,\Delta)<\infty$ and $\lambda=\lambda(\beta,B,\Delta)>0$ such that for every finite graph $G=(V,E)$ of maximal degree at most $\Delta$ there is a fixed point $\{\nu^*_{i\to j}\}$ of the BP iteration (2.10) such that, for any positive initial condition $\{\nu^{(0)}_{l\to k}\}$ and all $t\ge0$,
--   $$\sup_{(i,j)\in E}\big\|\nu^{(t)}_{i\to j}-\nu^*_{i\to j}\big\|_{\mathrm{TV}}\le A\exp(-\lambda t).$$
--
--   Belief propagation is the standard message-passing algorithm for approximating marginals of graphical models. The theorem guarantees, for ferromagnetic Ising models with a positive field, convergence at every temperature, at a rate that does not depend on the size or structure of the graph beyond its maximal degree.
--
--   **Formalization Note** The supremum is over directed edges $i\to j$ (both orientations of every edge) and is stated as a bound for each of them. The graph is finite. The fixed point is a family of distributions on $\{+1,-1\}$, one per directed edge, and the iterates are computed from the update (2.10).
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 7, Theorem 2.6, eq. (2.11)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_BPIteration

namespace IsingLTL.BeliefProp

/-- **Theorem 2.6** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*,
arXiv:0804.4726v3, p. 7, eq. (2.11)). Assume `β ≥ 0`, `B > 0` and `G` is a graph of finite maximal
degree `Δ`. Then there exist `A = A(β, B, Δ)` finite, `λ = λ(β, B, Δ) > 0` and a fixed point
`{ν*_{i→j}}` of the BP iteration (2.10) such that for any positive initial condition
`{ν^{(0)}_{l→k}}` and all `t ≥ 0`,
`sup_{(i,j)∈E} ‖ν^{(t)}_{i→j} − ν*_{i→j}‖_TV ≤ A exp(−λt)`.

Formalization Note: `A` and `λ` are chosen before the graph (they depend on `β, B, Δ` only).
The graph is finite (`Fintype V`) with all degrees `≤ Δ`. The fixed point is a family of
distributions on `{+1, −1}`, one per directed edge, with `bp ν* = ν*`; the BP iterates are
computed, `ν^{(t)} = bp^t ν^{(0)}`. The supremum over directed edges `i → j` (messages live on
directed edges, so `(i, j) ∈ E` covers both orientations) is stated as a bound for every directed
edge. `‖·‖_TV = ½ ℓ¹`. -/
theorem theorem_2_6_bp_convergence (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hB : 0 < B) :
    ∃ A lam : ℝ, 0 < lam ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ Δ) →
        ∃ νstar : V → V → Bool → ℝ, IsMsgFamily G νstar ∧ bp G β B νstar = νstar ∧
          ∀ ν0 : V → V → Bool → ℝ, IsMsgFamily G ν0 → IsPositiveMsg G ν0 →
            ∀ (t : ℕ) (i j : V), G.Adj i j →
              tvDist (bpIter G β B t ν0 i j) (νstar i j) ≤ A * Real.exp (-lam * t) := by sorry

end IsingLTL.BeliefProp
