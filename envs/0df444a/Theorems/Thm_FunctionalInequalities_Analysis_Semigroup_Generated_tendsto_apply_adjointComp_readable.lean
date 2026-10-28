-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_tendsto_apply_adjointComp_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_adjointComp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:08.248033+00:00
-- url     : https://prove2.me/theorems/6e54778c-ae6c-46bb-82a6-59cce5fb7b5a
-- title:
--   Strong Convergence on the Range of the Generator
-- statement:
--   This is an auxiliary strong-convergence statement for the generated semigroup.
--
--   Let $H_0,H_1$ be real complete inner-product spaces, let $T:H_0\to H_1$ be closed with dense domain, and write $A=T^\dagger T$. For every $y\in D(A)$,
--
--   $$
--   P_t(Ay)\longrightarrow0\qquad(t\to\infty).
--   $$
--
--   Thus the semigroup converges strongly to zero on vectors in the range of $A$.
--
--   This result is the basic range-level convergence estimate used in extending convergence to the closure of the range.
--
--   **Formalization Note.** The limit is expressed as `Tendsto` along real `t` tending to `atTop`; the semigroup is `Generated.apply T hT hd`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_apply_adjointComp (y : (adjointComp T).domain) :
--       Tendsto (fun t : ℝ => apply T hT hd t (adjointComp T y)) atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Convergence`](https://prove2.me/theorems/bf431053-eab1-4154-9189-5a728fdc5db2).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082).
--
--   Previous: [`mem_closure_range_of_inner_eq_zero`](https://prove2.me/theorems/2b0256b2-bcfd-472f-9590-a4b4f1fd87ee) · Next: [`tendsto_apply_of_mem_closure_range`](https://prove2.me/theorems/92de58e8-c90b-436c-a19f-8dc11ed44fbe).
--
--   [Source excerpt, lines 144–145](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L144-L145) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L143-L164 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Convergence`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_adjointComp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence

open Filter Topology Set
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_adjointComp_readable (y : (adjointComp T).domain) :
    Tendsto (fun t : ℝ => apply T hT hd t (adjointComp T y)) atTop (𝓝 0) := by sorry
