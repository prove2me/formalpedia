-- Prove2me | Theorems.Thm_Gomory69_Lifting_liftedPath_minimal
-- name    : Gomory69.Lifting.liftedPath_minimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:14:08.713187+00:00
-- url     : https://prove2.me/theorems/eec1096e-2339-4cd0-ab6e-ee458422f8db
-- title:
--   p. 487, proof of THEOREM 19 — each lifted path T_k(τ) solves the group equation and has cost π₀
-- statement:
--   Let $\psi:\mathcal G\to\mathcal H$ be a homomorphism of finite Abelian groups with kernel $\mathcal K$, and $\phi:\mathcal H\to\mathcal G$ a section, $\psi\phi(h)=h$ for every $h$. Let $g_0\in\mathcal G$, $\pi'\in\mathbb R^{\mathcal H^+}$, $\pi(g)=\pi'(\psi g)$ with $\pi'(\bar 0)=0$, and $\pi_0\in\mathbb R$. Let $\tau\in T(\mathcal H,\psi g_0)$ with $\pi'\cdot\tau=\pi_0$ and $k\in\mathcal K$. Then the closing element $c=g_0-\sum_{g\notin\mathcal K}t_k(g)\cdot g$ lies in $\mathcal K$, and the lifted path $T_k(\tau)$ satisfies
--
--   $$T_k(\tau)\in T(\mathcal G,g_0),\qquad \pi\cdot T_k(\tau)=\pi_0 .$$
--
--   Each minimal path of the quotient problem thus yields $|\mathcal K|$ minimal paths of the original problem, one for each $k$; these are the rows of the matrix of Fig. 6.
--
--   **Formalization Note** $T_k(\tau)$ is the vector `liftedPath ψ φ g₀ k τ` of the definition file; its kernel entry is a single $1$ on $c$ when $c\neq\bar 0$ and nothing when $c=\bar 0$. The page writes "$g=\phi(h)+k'$ with $h=\bar 0$ and $k'=c$"; the Lean places the $1$ on $c$ itself (the two agree when $\phi(\bar 0)=\bar 0$). "Minimal" is stated as cost exactly $\pi_0$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 487, proof of THEOREM 19

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting

theorem liftedPath_minimal {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (φ : H → G) (hφ : ∀ h, ψ (φ h) = h) (g₀ : G)
    (π' : Plus H → ℝ) (π₀ : ℝ) (τ : Plus H → ℕ) (hτ : τ ∈ T H (ψ g₀))
    (hτπ : π' ⬝ᵥ castVec τ = π₀) (k : G) (hk : ψ k = 0) :
    ψ (closingElement ψ φ g₀ k τ) = 0 ∧
      liftedPath ψ φ g₀ k τ ∈ T G g₀ ∧
        liftCoeff ψ π' ⬝ᵥ castVec (liftedPath ψ φ g₀ k τ) = π₀ := by sorry

end Gomory69.Lifting
