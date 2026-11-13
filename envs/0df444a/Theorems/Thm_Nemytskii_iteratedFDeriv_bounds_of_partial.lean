-- Prove2me | Theorems.Thm_Nemytskii_iteratedFDeriv_bounds_of_partial
-- name    : Nemytskii.iteratedFDeriv_bounds_of_partial
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T22:32:53.774571+00:00
-- url     : https://prove2.me/theorems/91884e19-7edb-43c4-9aff-dc6454d03dc1
-- title:
--   Derivative bounds for partial maps along a continuous parameter
-- statement:
--   Let $\Psi : P \times E \to F$ be $C^\infty$, $p : X \to P$ continuous, and suppose every derivative $D^k\Psi$ is bounded on $\{(p(x), a) : x \in X, \|a\| \le R\}$ for every $R$. Then for $\Phi(x, a) = \Psi(p(x), a)$: each $\Phi(x, \cdot)$ is $C^\infty$, and for every $k$ the derivative $(x, a) \mapsto D^k\Phi(x, \cdot)(a)$ is jointly continuous and bounded on $X \times \bar B_R(0)$ for every $R$.
--
--   **Role.** Verifies the hypotheses of `Nemytskii.exists_contDiff_superposition` from derivative bounds along a non-compact parameter.
-- source:
--   Superposition (Nemytskii) operators, cf. J. Appell and P. P. Zabrejko, Nonlinear Superposition Operators, Cambridge Univ. Press 1990; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20

import Mathlib

open Metric Set Filter Topology BoundedContinuousFunction
open scoped ContDiff

namespace Nemytskii

/-- If `Ψ : P × E → F` is `C^∞`, `p : X → P` is continuous, and every derivative of `Ψ` is
bounded on `range p × closedBall 0 R` for every `R`, then the partial maps `a ↦ Ψ (p x, a)` are
`C^∞`, and each of their derivatives is jointly continuous in `(x, a)` and bounded on
`X × closedBall 0 R` for every `R`. -/
theorem iteratedFDeriv_bounds_of_partial {X : Type*} [TopologicalSpace X]
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p)
    (hbd : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ ≤ C) :
    (∀ x, ContDiff ℝ ∞ ((fun x a => Ψ (p x, a)) x)) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) y.1) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) x) a‖ ≤ C := by
  sorry

end Nemytskii
