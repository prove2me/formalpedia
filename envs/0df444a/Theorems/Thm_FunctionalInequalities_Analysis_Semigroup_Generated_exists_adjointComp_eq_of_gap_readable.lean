-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_adjointComp_eq_of_gap_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:53.870822+00:00
-- url     : https://prove2.me/theorems/4fa4bc87-0c47-4025-88c0-329b6fe87034
-- title:
--   Solvability of the Adjoint-Composition Equation
-- statement:
--   This is an existence theorem for the equation $Au=g$ on the orthogonal complement of $\ker T$.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed with dense domain, and write $A=T^\dagger T$. Fix $C\in\mathbb{R}$ and assume the gap condition
--
--   $$\|y\|^2\le C\|Ty\|^2$$
--
--   for every $y\in D(T)$ orthogonal to $\ker T$. If $g\in H_0$ is orthogonal to every $k\in D(T)$ with $Tk=0$, then there exists $u\in D(A)$ such that
--
--   $$u\perp\ker T\qquad\text{and}\qquad Au=g.$$
--
--   This provides existence of an inverse on the kernel complement; uniqueness is supplied by the corresponding uniqueness lemma.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_adjointComp_eq_of_gap {C : ℝ}
--       (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
--         ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
--       (g : H₀) (hg : ∀ k : T.domain, T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
--       ∃ u : (adjointComp T).domain,
--         (∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) ∧ adjointComp T u = g
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Inverse`](https://prove2.me/theorems/947095ad-bada-4fd3-8b2d-3a6d8c455ee7).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a).
--
--   Supporting theorems: [`mem_closure_range_of_inner_eq_zero`](https://prove2.me/theorems/2b0256b2-bcfd-472f-9590-a4b4f1fd87ee), [`norm_le_of_gap`](https://prove2.me/theorems/bba069aa-666a-44e8-ad58-668fa76e9abb).
--
--   Previous: [`norm_le_of_gap`](https://prove2.me/theorems/bba069aa-666a-44e8-ad58-668fa76e9abb) · Next: [`eq_of_adjointComp_eq`](https://prove2.me/theorems/6574e2a9-9b4d-48e4-99c5-802eaa15ee6d).
--
--   [Source excerpt, lines 153–158](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L153-L158) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L150-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Inverse`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Inverse

open scoped InnerProductSpace RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
include hT hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap_readable {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (g : H₀) (hg : ∀ k : T.domain, T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    ∃ u : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) ∧ adjointComp T u = g := by sorry
