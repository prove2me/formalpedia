-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_mem_closure_range_of_inner_eq_zero_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:53.999641+00:00
-- url     : https://prove2.me/theorems/2b0256b2-bcfd-472f-9590-a4b4f1fd87ee
-- title:
--   Orthogonality to the Kernel Implies Closure of the Range
-- statement:
--   This is a range-closure characterization for $A=T^\dagger T$.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed, and assume $D(T)$ is dense in $H_0$. If $g\in H_0$ satisfies
--
--   $$\langle g,k\rangle=0$$
--
--   for every $k\in D(A)$ with $Ak=0$, where $A=\operatorname{adjointComp}(T)$, then
--
--   $$g\in\overline{\operatorname{range}(A)}.$$
--
--   The closure is taken in $H_0$. This is a standard Hilbert-space ingredient for approximation by the range of a self-adjoint operator.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem mem_closure_range_of_inner_eq_zero (g : H₀)
--       (hg : ∀ k : (adjointComp T).domain, adjointComp T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
--       g ∈ closure (Set.range fun y : (adjointComp T).domain => adjointComp T y)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Convergence`](https://prove2.me/theorems/bf431053-eab1-4154-9189-5a728fdc5db2).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a).
--
--   Supporting theorems: [`exists_mem_adjointComp_domain_of_inner_eq_zero`](https://prove2.me/theorems/edb92a6e-d8df-42b7-993b-006efcfa9b43).
--
--   Previous: [`exists_mem_adjointComp_domain_of_inner_eq_zero`](https://prove2.me/theorems/edb92a6e-d8df-42b7-993b-006efcfa9b43) · Next: [`tendsto_apply_adjointComp`](https://prove2.me/theorems/6e54778c-ae6c-46bb-82a6-59cce5fb7b5a).
--
--   [Source excerpt, lines 102–104](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L102-L104) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L100-L141 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Convergence`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence

open scoped RealInnerProductSpace LinearPMap
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
include hT hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_readable (g : H₀)
    (hg : ∀ k : (adjointComp T).domain, adjointComp T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    g ∈ closure (Set.range fun y : (adjointComp T).domain => adjointComp T y) := by sorry
