-- Prove2me | Theorems.Thm_Gomory69_Lifting_rank_D_sub_one
-- name    : Gomory69.Lifting.rank_D_sub_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:14:32.252354+00:00
-- url     : https://prove2.me/theorems/a1827a4a-a674-49af-97d1-db404d81537e
-- title:
--   pp. 487–488, proof of THEOREM 19 — the lifted inequality has D − 1 linearly independent minimal paths
-- statement:
--   Let $\psi$ be a homomorphism of the finite Abelian group $\mathcal G$ **onto** the finite Abelian group $\mathcal H$, with $\psi g_0\neq\bar 0$, let $D=|\mathcal G|$, and let $(\pi',\pi_0)$ be a face of $P(\mathcal H,\psi g_0)$ with $\pi_0>0$. Put $\pi(g)=\pi'(\psi g)$, $g\in\mathcal G^+$, with $\pi'(\bar 0)=0$. Then there are $D-1$ solutions $t^1,\dots,t^{D-1}\in T(\mathcal G,g_0)$ with
--
--   $$\pi\cdot t^i=\pi_0\quad(i=1,\dots,D-1)$$
--
--   that are linearly independent in $\mathbb R^{\mathcal G^+}$.
--
--   In the paper these are the lifted paths $T_k(\tau)$ over all $k\in\mathcal K$ and all $|\mathcal H|-1$ independent minimal paths $\tau$ of the quotient problem, together with one path for each nonzero $k\in\mathcal K$ obtained by adding $s(k)$ copies of $k$ to a lifted path. Together with the validity of the lift, this is what THEOREM 19 asserts.
--
--   **Formalization Note** The page says "for each $k\in\mathcal K$ a row"; $\bar 0$ has no column, so the rows are added for $k\in\mathcal K-\bar 0$, which is the count that gives $D-1$. The hypothesis $\pi_0>0$ is not on the page; without it the statement fails (see the goal theorem).
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 487–488, proof of THEOREM 19 (Figs. 6, 7)

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting

theorem rank_D_sub_one {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (hψ : Function.Surjective ψ) (g₀ : G) (hg₀ : ψ g₀ ≠ 0)
    (π' : Plus H → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (hface : IsFace H (ψ g₀) π' π₀) :
    ∃ s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ),
      (∀ i, s i ∈ T G g₀ ∧ liftCoeff ψ π' ⬝ᵥ castVec (s i) = π₀) ∧
        LinearIndependent ℝ (fun i => castVec (s i)) := by sorry

end Gomory69.Lifting
