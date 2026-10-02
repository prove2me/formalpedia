-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_holder_estimate
-- name    : HunterPDE.Newtonian.holder_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:30:50.302862+00:00
-- url     : https://prove2.me/theorems/a84c578c-16ea-4e67-8a4b-f3c20ee834ba
-- title:
--   Theorem 2.28 — Hölder estimate [∂ᵢⱼu]_{0,α} ≤ C [f]_{0,α} for the Newtonian potential
-- statement:
--   Let $n \ge 2$ and $0 < \alpha < 1$. There is a constant $C$, depending only on $\alpha$ and $n$, such that for every $f \in C_c^\infty(\mathbb{R}^n)$, with Newtonian potential $u = \Gamma * f$, and all indices $i, j$,
--   $$[\partial_{ij} u]_{0,\alpha} \le C\,[f]_{0,\alpha},$$
--   where $[\cdot]_{0,\alpha}$ is the Hölder seminorm (1.1) taken over all of $\mathbb{R}^n$.
--
--   This is the model Schauder estimate: inverting the Laplacian gains exactly two derivatives when regularity is measured in Hölder norms, whereas no such estimate holds in the maximum norm; the endpoint $\alpha = 1$ is excluded. It is the basis of Schauder's existence theory for elliptic equations with Hölder continuous coefficients.
--
--   **Formalization Note.** The constant $C \in [0, \infty)$ is quantified before $f$, $i$ and $j$, and after $n$ and $\alpha$. Seminorms take values in $[0, \infty]$; for $f \in C_c^\infty$ the right-hand side is finite, so the inequality asserts in particular that $\partial_{ij} u$ is uniformly $\alpha$-Hölder on $\mathbb{R}^n$. Indices are 0-based and $\partial_{ij} = \partial_i \partial_j$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 40, Theorem 2.28

import Mathlib
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_NewtonianPotential
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Definitions.Def_HunterPDE_Shared_HolderSeminorm

namespace HunterPDE.Newtonian

open scoped ContDiff ENNReal NNReal

/-- Hunter, *Notes on PDEs*, p. 40, Theorem 2.28 (Hölder estimate for the Newtonian potential):
for `n ≥ 2` and `0 < α < 1` there is a constant `C`, depending only on `α` and `n`, such that
for every `f ∈ C_c^∞(ℝⁿ)` and all `i, j`, the Newtonian potential `u = Γ ∗ f` satisfies
`[∂ᵢⱼu]_{0,α} ≤ C [f]_{0,α}`, the Hölder seminorms (1.1) being taken over all of `ℝⁿ`.
`C` is chosen before `f`, `i`, `j`; the seminorms are `ℝ≥0∞`-valued. -/
theorem holder_estimate (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ i j : Fin n,
        Shared.holderSeminorm α Set.univ (secondPartial (newtonianPotential n f) i j) ≤
          (C : ℝ≥0∞) * Shared.holderSeminorm α Set.univ f := by sorry

end HunterPDE.Newtonian
