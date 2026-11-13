-- Prove2me | Theorems.Thm_Nemytskii_exists_contDiff_superposition
-- name    : Nemytskii.exists_contDiff_superposition
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T22:24:07.472193+00:00
-- url     : https://prove2.me/theorems/e138c033-b9c8-450a-bf1c-71e2947459c8
-- title:
--   Superposition operators on bounded continuous functions are $C^\infty$
-- statement:
--   Let $X$ be a topological space, $E, F$ real normed spaces, and $\Phi : X \to E \to F$ such that each partial map $\Phi(x, \cdot)$ is $C^\infty$, and for every $k$ the $k$-th derivative $(x, a) \mapsto D^k\Phi(x, \cdot)(a)$ is jointly continuous on $X \times E$ and bounded on $X \times \bar B_R(0)$ for every $R$. Then there is a $C^\infty$ map $N : C_b(X, E) \to C_b(X, F)$ with $N(u)(x) = \Phi(x, u(x))$ for all $u$ and $x$.
--
--   **Role.** The basic smoothness statement for Nemytskii (superposition) operators on $C_b$: smooth nonlinear expressions in the values of a function define smooth maps of $C_b$, provided the value-derivatives are uniformly controlled on bounded sets.
-- source:
--   Superposition (Nemytskii) operators, cf. J. Appell and P. P. Zabrejko, Nonlinear Superposition Operators, Cambridge Univ. Press 1990; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20

import Mathlib

open Metric Set Filter Topology BoundedContinuousFunction
open scoped ContDiff

namespace Nemytskii

universe u v

/-- **Smoothness of superposition operators on bounded continuous functions.** Let
`Φ : X → E → F` be such that each `Φ x` is `C^∞` and, for every `k`, the `k`-th derivative
`(x, a) ↦ D^k (Φ x) a` is jointly continuous and bounded on `X × closedBall 0 R` for every `R`.
Then `u ↦ (x ↦ Φ x (u x))` is a `C^∞` map `(X →ᵇ E) → (X →ᵇ F)`. -/
theorem exists_contDiff_superposition {X : Type u} [TopologicalSpace X]
    {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : X → E → F)
    (hs : ∀ x, ContDiff ℝ ∞ (Φ x))
    (hc : ∀ k : ℕ, Continuous (fun p : X × E => iteratedFDeriv ℝ k (Φ p.1) p.2))
    (hb : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k (Φ x) a‖ ≤ C) :
    ∃ N : (X →ᵇ E) → (X →ᵇ F), ContDiff ℝ ∞ N ∧ ∀ u x, N u x = Φ x (u x) := by
  sorry

end Nemytskii
