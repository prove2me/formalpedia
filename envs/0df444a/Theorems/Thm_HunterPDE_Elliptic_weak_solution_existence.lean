-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_weak_solution_existence
-- name    : HunterPDE.Elliptic.weak_solution_existence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:49:59.592982+00:00
-- url     : https://prove2.me/theorems/71fd687c-89c7-4679-998f-30c61e33810e
-- title:
--   Theorem 4.22 — unique weak solution of Lu + μu = f for μ ≥ γ
-- statement:
--   Let $\Omega$ be an open set in $\mathbb{R}^n$ and $f \in H^{-1}(\Omega)$. Let $L$ be an operator (4.16) with coefficients satisfying (4.17), and let $\gamma \in \mathbb{R}$ be a constant for which Theorem 4.21 holds: there are $C_1, C_2 > 0$ with $C_1\|u\|_{H^1_0}^2 \le a(u,u) + \gamma\|u\|_{L^2}^2$ and $|a(u,v)| \le C_2\|u\|_{H^1_0}\|v\|_{H^1_0}$ for all $u, v$. Then for every $\mu \ge \gamma$ there is a unique weak solution $u \in H^1_0(\Omega)$ of the Dirichlet problem
--   $$Lu + \mu u = f, \qquad u \in H^1_0(\Omega),$$
--   in the sense of Definition 4.19: $a(u,\phi) + \mu(u,\phi)_{L^2} = \langle f,\phi\rangle$ for all $\phi \in H^1_0(\Omega)$.
--
--   This makes $L + \mu I$ invertible from $H^1_0(\Omega)$ onto $H^{-1}(\Omega)$ for large $\mu$ and so defines the resolvent.
--
--   **Formalization Note.** The page prints the equation as "$Lu + \mu f = 0$"; Definition 4.19 and the proof make it $Lu + \mu u = f$, which is what is stated. The hypothesis on $\gamma$ is the conclusion of Theorem 4.21 for that $\gamma$; uniform ellipticity is not assumed separately.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 105, Theorem 4.22

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

open MeasureTheory

namespace HunterPDE.Elliptic

/-- Theorem 4.22 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 105: let `Ω` be an open set
in `ℝⁿ`, `f ∈ H⁻¹(Ω)`, `L` an operator (4.16) with coefficients satisfying (4.17), and `γ ∈ ℝ` a
constant for which Theorem 4.21 holds (there are `C₁, C₂ > 0` with (4.23) and (4.24)). Then for
every `μ ≥ γ` there is a unique weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem
`Lu + μu = f` in the sense of Definition 4.19: `a(u, φ) + μ (u, φ)_{L²} = ⟨f, φ⟩` for all
`φ ∈ H¹₀(Ω)`.
The page prints the equation as `Lu + μf = 0`; Definition 4.19 and the proof make it
`Lu + μu = f`, which is what is stated. -/
theorem weak_solution_existence {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (P : Coeffs n) (hP : P.Admissible Ω) (γ : ℝ)
    (hγ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + γ * l2inner u u) ∧
      ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖)
    (f : StrongDual ℝ (H10 n Ω)) (μ : ℝ) (hμ : γ ≤ μ) :
    ∃! u : H10 n Ω, IsWeakSolution (form P) μ (fun φ => f φ) u := by sorry

end HunterPDE.Elliptic
