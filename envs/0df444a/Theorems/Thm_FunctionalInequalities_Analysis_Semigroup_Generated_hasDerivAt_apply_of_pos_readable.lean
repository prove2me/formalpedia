-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivAt_apply_of_pos_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:57.696081+00:00
-- url     : https://prove2.me/theorems/0091d156-a7c6-481a-96be-c117b4351bce
-- title:
--   Semigroup Orbit Derivative at Positive Times
-- statement:
--   This is the classical derivative formula for the generated semigroup orbit at positive times.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed with dense domain, and let $A=T^\dagger T$. For arbitrary $g\in H_0$ and every $t>0$, the orbit $s\mapsto P_s g$ is differentiable at $t$ and
--
--   $$\frac{d}{ds}\Big|_{s=t}P_s g=-A(P_t g).$$
--
--   The type asserts `HasDerivAt` at each strictly positive time and includes the domain witness establishing $P_tg\in D(A)$. No differentiability at $t=0$ is claimed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasDerivAt_apply_of_pos (g : H₀) {t : ℝ} (ht : 0 < t) :
--       HasDerivAt (fun s => apply T hT hd s g)
--         (-adjointComp T ⟨apply T hT hd t g, mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩) t
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/TimeDerivative`](https://prove2.me/theorems/b3d8e0b7-8cea-4a59-87d9-a8d37efcca52).
--
--   Definition modules: [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Analysis/Semigroup/Generated/Smoothing`](https://prove2.me/theorems/c524f398-2d2a-4ccf-863f-ec61695e2aa1), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082).
--
--   Supporting theorems: [`hasDerivWithinAt_apply_Iic`](https://prove2.me/theorems/bdda2388-4c72-4ec1-986b-50182a9524c4).
--
--   Previous: [`hasDerivWithinAt_apply_Iic`](https://prove2.me/theorems/bdda2388-4c72-4ec1-986b-50182a9524c4).
--
--   [Source excerpt, lines 330–332](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/TimeDerivative.lean#L330-L332) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/TimeDerivative.lean#L327-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_TimeDerivative

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_readable (g : H₀) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => apply T hT hd s g)
      (-adjointComp T ⟨apply T hT hd t g, mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩) t := by sorry
