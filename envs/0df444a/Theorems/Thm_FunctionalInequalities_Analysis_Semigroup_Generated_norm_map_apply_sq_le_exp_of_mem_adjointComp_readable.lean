-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_map_apply_sq_le_exp_of_mem_adjointComp_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_of_mem_adjointComp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:04.336056+00:00
-- url     : https://prove2.me/theorems/3e1e0324-94fa-4fd6-b2c3-3d7551ff2d12
-- title:
--   Exponential Energy Decay on the Operator Domain
-- statement:
--   This is the exponential energy estimate under an integrated curvature bound.
--
--   Let $H_0,H_1$ be real complete inner-product spaces, let $T:H_0\to H_1$ be closed with dense domain, and put $A=T^\dagger T$. Let $\rho\in\mathbb R$ and assume that for every $y\in D(A)$,
--
--   $$
--   \rho\,\|Ty\|^2\le \|Ay\|^2.
--   $$
--
--   Then for every $f\in D(A)$ and every $t\ge0$,
--
--   $$
--   \|T(P_t f)\|^2\le e^{-2\rho t}\,\|Tf\|^2,
--   $$
--
--   where $P_t$ is `Generated.apply T hT hd t`.
--
--   This is the domain-level energy-decay estimate from which the estimate on the whole form domain is obtained.
--
--   **Formalization Note.** The parameter $\rho$ is only assumed real; no positivity hypothesis on $\rho$ appears in the type.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_map_apply_sq_le_exp_of_mem_adjointComp {ρ : ℝ}
--       (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
--       (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
--       ‖T ⟨apply T hT hd t f, (preserves_domain T hT hd f ht).2⟩‖ ^ 2 ≤
--         Real.exp (-2 * ρ * t) * ‖T ⟨f, f.2.2⟩‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Curvature`](https://prove2.me/theorems/2d0d4681-a28b-4386-bf7f-208cba5fd2c8).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Analysis/Semigroup/Generated/Domain`](https://prove2.me/theorems/a5d40995-ce8a-4d58-a0cc-856898fdfa5c), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082).
--
--   Supporting theorems: [`continuousOn`](https://prove2.me/theorems/57737b97-6a96-46bc-a5a5-9aee7d9c818b), [`hasDerivAt_inner_apply`](https://prove2.me/theorems/f5643287-fcd8-4cb8-adec-bac864e18749), [`le_exp_mul_of_hasDerivAt_le`](https://prove2.me/theorems/38febeed-57be-4f77-b86b-1ca1d79ba62c), [`norm_map_apply_sq_eq_inner`](https://prove2.me/theorems/c2084695-8d99-499c-9d32-ea5e8a16d7be).
--
--   Previous: [`le_exp_mul_of_hasDerivAt_le`](https://prove2.me/theorems/38febeed-57be-4f77-b86b-1ca1d79ba62c) · Next: [`norm_map_apply_sq_le_exp`](https://prove2.me/theorems/8f943860-f6e7-4593-a4f7-2a7ee8a97f10).
--
--   [Source excerpt, lines 226–230](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L226-L230) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L225-L304 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_of_mem_adjointComp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_of_mem_adjointComp_readable {ρ : ℝ}
    (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
    (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T ⟨apply T hT hd t f, (preserves_domain T hT hd f ht).2⟩‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ‖T ⟨f, f.2.2⟩‖ ^ 2 := by sorry
