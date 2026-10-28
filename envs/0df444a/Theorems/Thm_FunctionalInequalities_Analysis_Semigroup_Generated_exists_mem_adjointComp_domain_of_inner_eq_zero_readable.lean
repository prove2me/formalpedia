-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_mem_adjointComp_domain_of_inner_eq_zero_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_of_inner_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:51.274888+00:00
-- url     : https://prove2.me/theorems/edb92a6e-d8df-42b7-993b-006efcfa9b43
-- title:
--   Kernel Membership from Orthogonality to the Operator Range
-- statement:
--   This is a self-adjointness lemma for $A=T^\dagger T$.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed, and assume $D(T)$ is dense in $H_0$. For $q\in H_0$, suppose
--
--   $$\langle q,Ay\rangle=0\quad\text{for every }y\in D(A),$$
--
--   where $A=\operatorname{adjointComp}(T)$. Then there exists a domain witness showing that $q\in D(A)$ and
--
--   $$Aq=0.$$
--
--   This technical result identifies vectors orthogonal to the range of the self-adjoint operator with its kernel.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_mem_adjointComp_domain_of_inner_eq_zero (q : H₀)
--       (hq : ∀ y : (adjointComp T).domain, ⟪q, adjointComp T y⟫ = 0) :
--       ∃ h : q ∈ (adjointComp T).domain, adjointComp T ⟨q, h⟩ = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Convergence`](https://prove2.me/theorems/bf431053-eab1-4154-9189-5a728fdc5db2).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a).
--
--   Next: [`mem_closure_range_of_inner_eq_zero`](https://prove2.me/theorems/2b0256b2-bcfd-472f-9590-a4b4f1fd87ee).
--
--   [Source excerpt, lines 64–66](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L64-L66) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L62-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Convergence`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_of_inner_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence

open scoped RealInnerProductSpace LinearPMap
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
include hT hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_of_inner_eq_zero_readable (q : H₀)
    (hq : ∀ y : (adjointComp T).domain, ⟪q, adjointComp T y⟫ = 0) :
    ∃ h : q ∈ (adjointComp T).domain, adjointComp T ⟨q, h⟩ = 0 := by sorry
