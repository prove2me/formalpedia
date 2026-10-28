-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivWithinAt_apply_Iic_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:52.668911+00:00
-- url     : https://prove2.me/theorems/bdda2388-4c72-4ec1-986b-50182a9524c4
-- title:
--   Left Semigroup Derivative on Positive Times
-- statement:
--   This is the left derivative formula for a generated semigroup orbit.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed with dense domain, let $A=T^\dagger T$, and let $f\in D(A)$. For $t>0$, the function $s\mapsto P_s f$ has a derivative at $t$ from the set $(-\infty,t]$:
--
--   $$\frac{d}{ds}\Big|_{s=t^-}P_s f=-A(P_t f).$$
--
--   Formally, `HasDerivWithinAt` is taken on `Iic t`, and the derivative is represented using the domain witness that $P_t f\in D(A)$. This is a one-sided derivative statement, not an unrestricted derivative assertion.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasDerivWithinAt_apply_Iic (f : (adjointComp T).domain) {t : ℝ} (ht : 0 < t) :
--       HasDerivWithinAt (fun s => apply T hT hd s f)
--         (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht.le⟩) (Iic t) t
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/TimeDerivative`](https://prove2.me/theorems/b3d8e0b7-8cea-4a59-87d9-a8d37efcca52).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Analysis/Semigroup/Generated/Domain`](https://prove2.me/theorems/a5d40995-ce8a-4d58-a0cc-856898fdfa5c), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082).
--
--   Supporting theorems: [`continuousOn`](https://prove2.me/theorems/57737b97-6a96-46bc-a5a5-9aee7d9c818b).
--
--   Next: [`hasDerivAt_apply_of_pos`](https://prove2.me/theorems/0091d156-a7c6-481a-96be-c117b4351bce).
--
--   [Source excerpt, lines 79–81](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/TimeDerivative.lean#L79-L81) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/TimeDerivative.lean#L77-L115 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_TimeDerivative

open Filter Topology Set
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic_readable (f : (adjointComp T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s => apply T hT hd s f)
      (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht.le⟩) (Iic t) t := by sorry
