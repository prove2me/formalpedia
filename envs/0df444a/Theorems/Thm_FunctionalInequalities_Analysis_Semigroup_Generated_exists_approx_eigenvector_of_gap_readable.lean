-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_approx_eigenvector_of_gap_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:52.14718+00:00
-- url     : https://prove2.me/theorems/96ac6eeb-d36c-4b96-80f6-6688bd059a47
-- title:
--   Approximate Eigenvectors at the Bottom of the Operator Spectrum
-- statement:
--   This is an approximate-eigenvector construction for $A=T^\dagger T$.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed with dense domain, and let $\lambda,\eta\in\mathbb{R}$ with $\lambda>0$. Assume:
--
--   1. For every $y\in D(T)$ orthogonal to $\ker T$, $\lambda\|y\|^2\le\|Ty\|^2$.
--   2. $y\in D(T)$ is orthogonal to $\ker T$.
--   3. $\|y\|=1$.
--   4. $\|Ty\|^2\le\lambda(1+\eta)$.
--
--   Then there exists $z\in D(A)$, orthogonal to $\ker T$, such that
--
--   $$\|y-z\|\le\sqrt{\eta/8},$$
--   $$\|Az-\lambda z\|\le\lambda\sqrt{\eta/2}.$$
--
--   The theorem does not assume $\eta\ge0$ in its type and does not assert the existence of an exact eigenvector.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_approx_eigenvector_of_gap (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
--       (hd : Dense (T.domain : Set H₀)) {lam η : ℝ} (hlam : 0 < lam)
--       (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
--         lam * ‖(y : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2)
--       (y : T.domain) (hy : ∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0)
--       (hy1 : ‖(y : H₀)‖ = 1) (hTy : ‖T y‖ ^ 2 ≤ lam * (1 + η)) :
--       ∃ z : (adjointComp T).domain,
--         (∀ k : T.domain, T k = 0 → ⟪(z : H₀), (k : H₀)⟫ = 0) ∧
--         ‖(y : H₀) - (z : H₀)‖ ≤ Real.sqrt (η / 8) ∧
--         ‖adjointComp T z - lam • (z : H₀)‖ ≤ lam * Real.sqrt (η / 2)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/ApproximateEigenvector`](https://prove2.me/theorems/18a59241-5071-4855-ad29-f2b977bc7191).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a).
--
--   [Source excerpt, lines 55–64](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/ApproximateEigenvector.lean#L55-L64) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/ApproximateEigenvector.lean#L49-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.ApproximateEigenvector`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_ApproximateEigenvector

open scoped InnerProductSpace RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

theorem FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap_readable (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {lam η : ℝ} (hlam : 0 < lam)
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      lam * ‖(y : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2)
    (y : T.domain) (hy : ∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0)
    (hy1 : ‖(y : H₀)‖ = 1) (hTy : ‖T y‖ ^ 2 ≤ lam * (1 + η)) :
    ∃ z : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(z : H₀), (k : H₀)⟫ = 0) ∧
      ‖(y : H₀) - (z : H₀)‖ ≤ Real.sqrt (η / 8) ∧
      ‖adjointComp T z - lam • (z : H₀)‖ ≤ lam * Real.sqrt (η / 2) := by sorry
