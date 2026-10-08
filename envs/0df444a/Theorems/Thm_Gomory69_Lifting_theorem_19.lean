-- Prove2me | Theorems.Thm_Gomory69_Lifting_theorem_19
-- name    : Gomory69.Lifting.theorem_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:14:01.50362+00:00
-- url     : https://prove2.me/theorems/3491354e-5166-4b72-8c0a-2dbca18737ef
-- title:
--   THEOREM 19, p. 486 — a face of P(H, ψg₀) lifts through a homomorphism ψ of G onto H to a face of P(G, g₀)
-- statement:
--   Let $\mathcal G$ and $\mathcal H$ be finite Abelian groups and $\psi$ a homomorphism of $\mathcal G$ **onto** $\mathcal H$ with kernel $\mathcal K$, and let $g_0\in\mathcal G$ with $g_0\notin\mathcal K$. Let $(\pi',\pi_0)$ be a face of the master polyhedron $P(\mathcal H,\psi g_0)$ with $\pi_0>0$. Define $\pi$ on $\mathcal G^+$ by
--
--   $$\pi(g)=\pi'(\psi g),\qquad\text{with }\pi'(\bar 0)=0,\ \text{so }\pi(g)=0\text{ for }g\in\mathcal K .$$
--
--   Then $(\pi,\pi_0)$ is a face of $P(\mathcal G,g_0)$.
--
--   Faces of the master polyhedron of a small group thus produce faces of the master polyhedra of all groups mapping onto it. For example, the face $t_1\ge 1$ of $P(\mathcal G_2,(1))$ lifts through reduction mod $2$ to the face $t_1+0t_2+t_3+0t_4+t_5\ge 1$ of $P(\mathcal G_6,(5))$ (p. 488). THEOREM 20 gives the converse for faces with a zero coefficient.
--
--   **Formalization Note** The hypothesis $\pi_0>0$ is **added**: the page does not state it, and without it the theorem is false under the paper's own definition of face. With $\mathcal G=\mathbb Z_6$, $\mathcal H=\mathbb Z_3$, $\psi$ reduction mod 3 and $g_0=1$, the inequality $t(1)\ge 0$ is a face of $P(\mathbb Z_3,(1))$ (THEOREM 16), but its lift $t(1)+t(4)\ge 0$ is not a face of $P(\mathbb Z_6,(1))$: its tight solutions all have $t(1)=t(4)=0$ and span only a 3-dimensional subspace of the 4-dimensional hyperplane. The proof's "$|\mathcal H|-1$ independent minimal paths" (p. 487) requires $\pi_0>0$. Surjectivity is the page's "onto"; $g_0\notin\mathcal K$ is written $\psi g_0\neq\bar 0$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 486, THEOREM 19 (proof pp. 486–488)

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting

theorem theorem_19 {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (hψ : Function.Surjective ψ) (g₀ : G) (hg₀ : ψ g₀ ≠ 0)
    (π' : Plus H → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (hface : IsFace H (ψ g₀) π' π₀) :
    IsFace G g₀ (liftCoeff ψ π') π₀ := by sorry

end Gomory69.Lifting
