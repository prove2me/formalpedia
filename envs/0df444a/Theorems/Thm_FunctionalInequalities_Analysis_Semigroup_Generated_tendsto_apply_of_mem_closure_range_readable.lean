-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_tendsto_apply_of_mem_closure_range_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_of_mem_closure_range_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:04.697185+00:00
-- url     : https://prove2.me/theorems/92de58e8-c90b-436c-a19f-8dc11ed44fbe
-- title:
--   Strong Convergence on the Closure of the Generator Range
-- statement:
--   This is an auxiliary strong-convergence statement for the generated semigroup.
--
--   Let $H_0,H_1$ be real complete inner-product spaces, let $T:H_0\to H_1$ be closed with dense domain, and write $A=T^\dagger T$. If $g\in H_0$ belongs to the closure of the range of $A$, then
--
--   $$
--   P_t g\longrightarrow0\qquad(t\to\infty).
--   $$
--
--   The statement provides the closure-extension step for ergodic convergence of the semigroup.
--
--   **Formalization Note.** Membership is in `closure (Set.range fun y => adjointComp T y)`, and convergence is expressed in the norm topology on $H_0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_apply_of_mem_closure_range {g : H₀}
--       (hg : g ∈ closure (Set.range fun y : (adjointComp T).domain => adjointComp T y)) :
--       Tendsto (fun t : ℝ => apply T hT hd t g) atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Convergence`](https://prove2.me/theorems/bf431053-eab1-4154-9189-5a728fdc5db2).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082).
--
--   Supporting theorems: [`tendsto_apply_adjointComp`](https://prove2.me/theorems/6e54778c-ae6c-46bb-82a6-59cce5fb7b5a).
--
--   Previous: [`tendsto_apply_adjointComp`](https://prove2.me/theorems/6e54778c-ae6c-46bb-82a6-59cce5fb7b5a).
--
--   [Source excerpt, lines 167–169](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L167-L169) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L166-L205 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Convergence`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_of_mem_closure_range`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence

open Filter Topology Set
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_of_mem_closure_range_readable {g : H₀}
    (hg : g ∈ closure (Set.range fun y : (adjointComp T).domain => adjointComp T y)) :
    Tendsto (fun t : ℝ => apply T hT hd t g) atTop (𝓝 0) := by sorry
