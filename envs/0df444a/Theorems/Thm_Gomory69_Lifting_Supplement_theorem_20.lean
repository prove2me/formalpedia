-- Prove2me | Theorems.Thm_Gomory69_Lifting_Supplement_theorem_20
-- name    : Gomory69.Lifting.Supplement.theorem_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:28:53.648847+00:00
-- url     : https://prove2.me/theorems/ac118980-daa3-4289-ba21-fb11686a9520
-- title:
--   THEOREM 20, p. 489 — a nontrivial face of P(G, g₀) with a zero coefficient is lifted from a face of a proper quotient
-- statement:
--   Let $\mathcal G$ be a finite Abelian group, $g_0\in\mathcal G$, and let $(\pi,\pi_0)$ be a nontrivial face of $P(\mathcal G,g_0)$, i.e. a face with $\pi_0>0$. Suppose $\pi(g)=0$ for some $g\neq\bar 0$. Then there are a finite Abelian group $\mathcal H$, a homomorphism $\psi$ of $\mathcal G$ onto $\mathcal H$ with $\psi g=\bar 0$, and a face $(\pi',\pi_0)$ of $P(\mathcal H,\psi g_0)$ such that
--
--   $$\pi(g')=\pi'(\psi g')\quad\text{for all }g'\in\mathcal G^+,\qquad\pi'(\bar 0)=0 .$$
--
--   This is the converse of THEOREM 19: every nontrivial face with a zero component is obtained by lifting a face of a smaller group.
--
--   **Formalization Note** The page names the face $(\pi_1,\pi_0)$ and then writes $\pi$; $\pi_1$ is read as $\pi$ (the proof uses $\pi_1$ for a path value). "Nontrivial" is read as $\pi_0>0$, as in the proof's use of subadditivity. The page's $h_0$ is $\psi g_0$. The conclusion requires $\psi g=\bar 0$: the theorem's existence claim would otherwise be met by $\mathcal H=\mathcal G$, $\psi=\mathrm{id}$, and the proof's $\mathcal H=\mathcal G/\mathcal K$ with $\mathcal K=\{g:\pi(g)=0\}\cup\{\bar 0\}$ satisfies it. The definition of $T(\mathcal G,\bar 0)$ excludes $t=0$, as the paper requires.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 489, THEOREM 20 (proof pp. 489–490)

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting.Supplement

universe u

theorem theorem_20 {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π : Plus G → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀)
    (hface : IsFace G g₀ π π₀) (g : Plus G) (hg : π g = 0) :
    ∃ (H : Type u) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
      (ψ : G →+ H) (π' : Plus H → ℝ),
      Function.Surjective ψ ∧ ψ (g : G) = 0 ∧ IsFace H (ψ g₀) π' π₀ ∧
        π = liftCoeff ψ π' := by sorry

end Gomory69.Lifting.Supplement
