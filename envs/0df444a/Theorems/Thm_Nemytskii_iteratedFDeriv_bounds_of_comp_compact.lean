-- Prove2me | Theorems.Thm_Nemytskii_iteratedFDeriv_bounds_of_comp_compact
-- name    : Nemytskii.iteratedFDeriv_bounds_of_comp_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T22:30:14.421317+00:00
-- url     : https://prove2.me/theorems/b6a2cd38-95ca-41d9-a006-643b18c2c842
-- title:
--   Derivative bounds for partial maps along a compact parameter
-- statement:
--   Let $P, E$ be proper real normed spaces, $F$ a real normed space, $\Psi : P \times E \to F$ of class $C^\infty$, and $p : X \to P$ continuous with values in a compact set $K$. Then for $\Phi(x, a) = \Psi(p(x), a)$: each $\Phi(x, \cdot)$ is $C^\infty$, and for every $k$ the derivative $(x, a) \mapsto D^k\Phi(x, \cdot)(a)$ is jointly continuous and bounded on $X \times \bar B_R(0)$ for every $R$.
--
--   **Role.** Verifies the hypotheses of `Nemytskii.exists_contDiff_superposition` for integrands that depend on $x$ through a compact parameter.
-- source:
--   Superposition (Nemytskii) operators, cf. J. Appell and P. P. Zabrejko, Nonlinear Superposition Operators, Cambridge Univ. Press 1990; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20

import Mathlib

open Metric Set Filter Topology BoundedContinuousFunction
open scoped ContDiff

namespace Nemytskii

/-- If `Ψ : P × E → F` is `C^∞` (with `P`, `E` proper) and `p : X → P` is continuous with values
in a compact set, then the partial maps `a ↦ Ψ (p x, a)` are `C^∞`, and each of their derivatives
is jointly continuous in `(x, a)` and bounded on `X × closedBall 0 R` for every `R`. -/
theorem iteratedFDeriv_bounds_of_comp_compact {X : Type*} [TopologicalSpace X]
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p) (K : Set P)
    (hK : IsCompact K) (hpK : ∀ x, p x ∈ K) :
    (∀ x, ContDiff ℝ ∞ ((fun x a => Ψ (p x, a)) x)) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) y.1) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k ((fun x a => Ψ (p x, a)) x) a‖ ≤ C := by
  sorry

end Nemytskii
