-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_le_of_gap_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:56.287334+00:00
-- url     : https://prove2.me/theorems/bba069aa-666a-44e8-ad58-668fa76e9abb
-- title:
--   Operator-Domain Bounds from a Kernel-Complement Gap
-- statement:
--   This is the norm and energy estimate obtained from a gap inequality.
--
--   Let $H_0,H_1$ be real Hilbert spaces, let $T:H_0\to H_1$ be a linear partial map with dense domain, and let $A=T^\dagger T$. Fix $C\in\mathbb{R}$. Assume that every $y\in D(T)$ orthogonal to $\ker T$ satisfies
--
--   $$\|y\|^2\le C\|Ty\|^2.$$
--
--   For every $u\in D(A)$ orthogonal to $\ker T$, the conclusion is
--
--   $$\|u\|\le C\|Au\|,$$
--   $$\|Tu\|^2=\langle Au,u\rangle,$$
--   $$\langle Au,u\rangle\le C\|Au\|^2.$$
--
--   The statement includes the case of arbitrary real $C$; no positivity assumption on $C$ appears in the type.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_le_of_gap {C : ℝ}
--       (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
--         ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
--       (u : (adjointComp T).domain)
--       (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) :
--       ‖(u : H₀)‖ ≤ C * ‖adjointComp T u‖ ∧
--         ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 = ⟪adjointComp T u, (u : H₀)⟫ ∧
--         ⟪adjointComp T u, (u : H₀)⟫ ≤ C * ‖adjointComp T u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Inverse`](https://prove2.me/theorems/947095ad-bada-4fd3-8b2d-3a6d8c455ee7).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a).
--
--   Next: [`exists_adjointComp_eq_of_gap`](https://prove2.me/theorems/4fa4bc87-0c47-4025-88c0-329b6fe87034).
--
--   [Source excerpt, lines 27–34](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L27-L34) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L23-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Inverse`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Inverse

open scoped InnerProductSpace RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
omit [CompleteSpace H₁]
include hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_readable {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (u : (adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) :
    ‖(u : H₀)‖ ≤ C * ‖adjointComp T u‖ ∧
      ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 = ⟪adjointComp T u, (u : H₀)⟫ ∧
      ⟪adjointComp T u, (u : H₀)⟫ ≤ C * ‖adjointComp T u‖ ^ 2 := by sorry
