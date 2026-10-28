-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_eq_of_adjointComp_eq_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:57.168367+00:00
-- url     : https://prove2.me/theorems/6574e2a9-9b4d-48e4-99c5-802eaa15ee6d
-- title:
--   Uniqueness on the Orthogonal Complement of the Kernel
-- statement:
--   This is a uniqueness lemma for the operator $A=T^\dagger T$.
--
--   Let $H_0,H_1$ be real Hilbert spaces, with $H_0$ complete, and let $T:H_0\to H_1$ be a linear partial map whose domain is dense in $H_0$. Let $u,v$ belong to the domain of `adjointComp T`, and assume:
--
--   1. $u$ is orthogonal to every $k\in D(T)$ satisfying $Tk=0$.
--   2. $v$ is orthogonal to every such $k$.
--   3. $Au=Av$, where $A=\operatorname{adjointComp}(T)$.
--
--   Then
--
--   $$u=v.$$
--
--   The conclusion identifies two operator-domain vectors with the same image under $T^\dagger T$ once both are orthogonal to $\ker T$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem eq_of_adjointComp_eq (u v : (adjointComp T).domain)
--       (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0)
--       (hv : ∀ k : T.domain, T k = 0 → ⟪(v : H₀), (k : H₀)⟫ = 0)
--       (huv : adjointComp T u = adjointComp T v) : (u : H₀) = v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Inverse`](https://prove2.me/theorems/947095ad-bada-4fd3-8b2d-3a6d8c455ee7).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a).
--
--   Previous: [`exists_adjointComp_eq_of_gap`](https://prove2.me/theorems/4fa4bc87-0c47-4025-88c0-329b6fe87034).
--
--   [Source excerpt, lines 240–243](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L240-L243) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L236-L259 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Inverse`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Inverse

open scoped InnerProductSpace RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
omit [CompleteSpace H₁]
include hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq_readable (u v : (adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0)
    (hv : ∀ k : T.domain, T k = 0 → ⟪(v : H₀), (k : H₀)⟫ = 0)
    (huv : adjointComp T u = adjointComp T v) : (u : H₀) = v := by sorry
