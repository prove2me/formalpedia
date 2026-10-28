-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_map_apply_sq_eq_inner_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_eq_inner_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:04.988017+00:00
-- url     : https://prove2.me/theorems/c2084695-8d99-499c-9d32-ea5e8a16d7be
-- title:
--   Semigroup Energy as an Inner Product
-- statement:
--   This is an auxiliary energy identity for a generated semigroup.
--
--   Let $H_0,H_1$ be real complete inner-product spaces, let $T:H_0\to H_1$ be closed with dense domain, and write $A=T^\dagger T$. For $f\in D(A)$ and $r\ge0$, let $P_r f$ be `Generated.apply T hT hd r f`. Then
--
--   $$
--   \|T(P_r f)\|^2=\langle P_r(Af),P_r f\rangle.
--   $$
--
--   The identity rewrites the squared form energy along the flow as an inner product, enabling differentiation and curvature estimates.
--
--   **Formalization Note.** The operator domains are represented by subtypes, and the norm and inner product are real-valued.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_map_apply_sq_eq_inner (f : (adjointComp T).domain) {r : ℝ} (hr : 0 ≤ r) :
--       ‖T ⟨apply T hT hd r f, (preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
--         ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Curvature`](https://prove2.me/theorems/2d0d4681-a28b-4386-bf7f-208cba5fd2c8).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Analysis/Semigroup/Generated/Domain`](https://prove2.me/theorems/a5d40995-ce8a-4d58-a0cc-856898fdfa5c), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082).
--
--   Next: [`hasDerivAt_inner_apply`](https://prove2.me/theorems/f5643287-fcd8-4cb8-adec-bac864e18749).
--
--   [Source excerpt, lines 34–36](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L34-L36) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L33-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_eq_inner`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature

open scoped RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_eq_inner_readable (f : (adjointComp T).domain) {r : ℝ} (hr : 0 ≤ r) :
    ‖T ⟨apply T hT hd r f, (preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
      ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫ := by sorry
