-- Prove2me | Theorems.Thm_Nemytskii_iteratedFDeriv_bounds_comp_clm
-- name    : Nemytskii.iteratedFDeriv_bounds_comp_clm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T22:30:14.704283+00:00
-- url     : https://prove2.me/theorems/1ccb2bea-ff49-459a-bb72-fa93fa29258a
-- title:
--   Derivative bounds are preserved by a bounded linear rescaling of the value
-- statement:
--   Let $\Psi : X \to E' \to F$ have $C^\infty$ partial maps whose derivatives of every order are jointly continuous on $X \times E'$ and bounded on $X \times \bar B_R(0)$ for every $R$. Let $L : X \to (E \to_L E')$ be continuous with $\|L(x)\| \le \Lambda$. Then $\Phi(x, a) = \Psi(x, L(x)a)$ has the same properties on $X \times E$.
--
--   **Role.** A closure property of the hypotheses of `Nemytskii.exists_contDiff_superposition`, used when the unknown enters through an $x$-dependent bounded weight.
-- source:
--   Superposition (Nemytskii) operators, cf. J. Appell and P. P. Zabrejko, Nonlinear Superposition Operators, Cambridge Univ. Press 1990; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20

import Mathlib

open Metric Set Filter Topology BoundedContinuousFunction
open scoped ContDiff

namespace Nemytskii

/-- Let `Ψ : X → E' → F` have `C^∞` partial maps whose derivatives of every order are jointly
continuous and bounded on `X × closedBall 0 R` for every `R`, and let `L : X → E →L[ℝ] E'` be
continuous and bounded. Then `(x, a) ↦ Ψ x (L x a)` has the same properties. -/
theorem iteratedFDeriv_bounds_comp_clm {X : Type*} [TopologicalSpace X]
    {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : X → E' → F) (hs : ∀ x, ContDiff ℝ ∞ (Ψ x))
    (hc : ∀ k : ℕ, Continuous (fun p : X × E' => iteratedFDeriv ℝ k (Ψ p.1) p.2))
    (hb : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E') R,
      ‖iteratedFDeriv ℝ k (Ψ x) a‖ ≤ C)
    (L : X → E →L[ℝ] E') (hL : Continuous L) (Λ : ℝ) (hΛ : ∀ x, ‖L x‖ ≤ Λ) :
    (∀ x, ContDiff ℝ ∞ ((fun x a => Ψ x (L x a)) x)) ∧
      (∀ k : ℕ, Continuous (fun y : X × E => iteratedFDeriv ℝ k ((fun x a => Ψ x (L x a)) y.1) y.2)) ∧
      ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
        ‖iteratedFDeriv ℝ k ((fun x a => Ψ x (L x a)) x) a‖ ≤ C := by
  sorry

end Nemytskii
