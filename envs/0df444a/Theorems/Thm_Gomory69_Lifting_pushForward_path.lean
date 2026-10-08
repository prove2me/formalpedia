-- Prove2me | Theorems.Thm_Gomory69_Lifting_pushForward_path
-- name    : Gomory69.Lifting.pushForward_path
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:13:50.103505+00:00
-- url     : https://prove2.me/theorems/5c188ec9-ae32-4541-9ecc-c28bf5b520b9
-- title:
--   p. 486, proof of THEOREM 19 — pushing a path forward along ψ preserves its cost, so the lifted inequality is valid
-- statement:
--   Let $\psi:\mathcal G\to\mathcal H$ be a homomorphism of finite Abelian groups, $g_0\in\mathcal G$ with $\psi g_0\ne\bar 0$, $\pi'\in\mathbb R^{\mathcal H^+}$ and $\pi(g)=\pi'(\psi g)$ with $\pi'(\bar 0)=0$. For $t\in\mathbb N^{\mathcal G^+}$ let $\tau(h)=\sum_{g\in\psi^{-1}h}t(g)$, $h\in\mathcal H^+$.
--
--   1. If $t\in T(\mathcal G,g_0)$, then $\tau\in T(\mathcal H,\psi g_0)$ and
--   $$\sum_{g\in\mathcal G^+}\pi(g)\,t(g)=\sum_{h\in\mathcal H^+}\pi'(h)\,\tau(h).$$
--   2. Consequently, for every $\pi_0\in\mathbb R$: if $\pi'\cdot\tau\ge\pi_0$ for all $\tau\in T(\mathcal H,\psi g_0)$, then $\pi\cdot t\ge\pi_0$ for all $t\in T(\mathcal G,g_0)$.
--
--   This is the half of THEOREM 19 that says the lifted inequality is valid for $P(\mathcal G,g_0)$; the elements of the kernel drop out of $\tau$ because their cost $\pi'(\bar 0)$ is $0$.
--
--   **Formalization Note** The paper argues with a path of value $\pi_1<\pi_0$ and derives a contradiction; the Lean states the underlying identity and the resulting implication directly. Paths are vectors $t$, their value is $\pi\cdot t$. The hypothesis $\psi g_0\ne\bar 0$ is from THEOREM 19; it ensures the pushed-forward path is nonzero and hence belongs to the paper's $T(\mathcal H,\psi g_0)$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 486, proof of THEOREM 19

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting

theorem pushForward_path {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (g₀ : G) (hg₀ : ψ g₀ ≠ 0) (π' : Plus H → ℝ) (π₀ : ℝ) :
    (∀ t ∈ T G g₀, pushForward ψ t ∈ T H (ψ g₀) ∧
        liftCoeff ψ π' ⬝ᵥ castVec t = π' ⬝ᵥ castVec (pushForward ψ t)) ∧
      ((∀ τ ∈ T H (ψ g₀), π₀ ≤ π' ⬝ᵥ castVec τ) →
        ∀ t ∈ T G g₀, π₀ ≤ liftCoeff ψ π' ⬝ᵥ castVec t) := by sorry

end Gomory69.Lifting
