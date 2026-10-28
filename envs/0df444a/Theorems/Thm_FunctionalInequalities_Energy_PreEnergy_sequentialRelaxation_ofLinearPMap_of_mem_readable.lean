-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_ofLinearPMap_of_mem_readable
-- name    : FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:43.500663+00:00
-- url     : https://prove2.me/theorems/416527b0-b0d6-435c-8137-3e2f122e7c5a
-- title:
--   Exact Relaxed Energy On The Closure Domain
-- statement:
--   This theorem identifies the sequential relaxation of a closable partial linear operator on the domain of its closure.
--
--   Let $X$ be a real normed space, let $H$ be a complete real Hilbert space, and let $T:X\dashrightarrow H$ be closable. For every $x\in\operatorname{dom}(\overline T)$,
--
--   $$
--   \operatorname{sequentialRelaxation}_{T}(x)
--   =
--   \|\overline T x\|_{+}^{\,2}.
--   $$
--
--   The left side is the `ENNReal`-valued sequential relaxation of the pre-energy `PreEnergy.ofLinearPMap T`; the right side is the square of the `NNReal` norm, coerced to `ENNReal`. The declaration is `sequentialRelaxation_ofLinearPMap_of_mem_readable`, and the equality is asserted only for points in the closure domain.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.PreEnergy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sequentialRelaxation_ofLinearPMap_of_mem (hT : T.IsClosable) (x : T.closure.domain) :
--       (ofLinearPMap T).sequentialRelaxation x = (‖T.closure x‖₊ ^ 2 : NNReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Relaxation/LinearPMap`](https://prove2.me/theorems/2ed50aac-81dd-45da-b8c8-597e80695a44).
--
--   Definition modules: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Supporting theorems: [`mem_closure_domain_of_frequently`](https://prove2.me/theorems/6c7672bb-0bd5-403e-8d31-fa2f5f6b54ca), [`sequentialRelaxation_ofLinearPMap_le`](https://prove2.me/theorems/2e69ddca-a539-4bb5-8778-3f0a7a70ba16).
--
--   Previous: [`sequentialRelaxation_ofLinearPMap_of_notMem`](https://prove2.me/theorems/e3ef01ee-0dd8-45ce-bd89-f6b6714c8f87).
--
--   [Source excerpt, lines 358–359](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L358-L359) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L357-L382 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LinearPMap`, declaration `FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : X →ₗ.[ℝ] H)

theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem_readable (hT : T.IsClosable) (x : T.closure.domain) :
    (ofLinearPMap T).sequentialRelaxation x = (‖T.closure x‖₊ ^ 2 : NNReal) := by sorry
