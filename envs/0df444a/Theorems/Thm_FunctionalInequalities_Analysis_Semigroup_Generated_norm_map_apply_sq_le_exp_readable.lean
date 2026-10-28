-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_map_apply_sq_le_exp_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:14.782502+00:00
-- url     : https://prove2.me/theorems/8f943860-f6e7-4593-a4f7-2a7ee8a97f10
-- title:
--   Exponential Energy Decay on the Form Domain
-- statement:
--   This is the exponential energy estimate on the full form domain under the curvature bound.
--
--   Let $H_0,H_1$ be real complete inner-product spaces, let $T:H_0\to H_1$ be closed with dense domain, and set $A=T^\dagger T$. Let $\rho\in\mathbb R$ and assume
--
--   $$
--   \rho\,\|Ty\|^2\le\|Ay\|^2\qquad\text{for every }y\in D(A).
--   $$
--
--   Then for every $f\in D(T)$ and every $t\ge0$,
--
--   $$
--   \|T(P_t f)\|^2\le e^{-2\rho t}\,\|Tf\|^2.
--   $$
--
--   This extends the decay estimate from $D(A)$ to $D(T)$ and is the principal semigroup energy estimate in this development.
--
--   **Formalization Note.** The conclusion concerns the form domain $D(T)$, while the curvature hypothesis ranges over $D(A)$; $P_t$ is `Generated.apply T hT hd t`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_map_apply_sq_le_exp {ρ : ℝ}
--       (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
--       (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
--       ‖T ⟨apply T hT hd t f, preserves_form_domain T hT hd f ht⟩‖ ^ 2 ≤
--         Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Curvature`](https://prove2.me/theorems/2d0d4681-a28b-4386-bf7f-208cba5fd2c8).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Analysis/Semigroup/Generated/FormDomain`](https://prove2.me/theorems/1bad6be8-1b71-47ad-839b-2965f4bb0242), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082).
--
--   Supporting theorems: [`norm_map_apply_sq_le_exp_of_mem_adjointComp`](https://prove2.me/theorems/3e1e0324-94fa-4fd6-b2c3-3d7551ff2d12).
--
--   Previous: [`norm_map_apply_sq_le_exp_of_mem_adjointComp`](https://prove2.me/theorems/3e1e0324-94fa-4fd6-b2c3-3d7551ff2d12) · Next: [`norm_sq_sub_norm_apply_sq_le`](https://prove2.me/theorems/d85e3676-603e-4937-ac22-4f0ac1d2765d).
--
--   [Source excerpt, lines 307–311](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L307-L311) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L306-L427 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_readable {ρ : ℝ}
    (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
    (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T ⟨apply T hT hd t f, preserves_form_domain T hT hd f ht⟩‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2 := by sorry
