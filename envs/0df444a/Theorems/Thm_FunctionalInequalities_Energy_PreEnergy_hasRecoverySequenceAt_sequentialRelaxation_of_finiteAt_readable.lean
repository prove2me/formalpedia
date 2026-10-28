-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_readable
-- name    : FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:47.027931+00:00
-- url     : https://prove2.me/theorems/49819e5c-83c3-4828-a8ce-20685b8af434
-- title:
--   Recovery Sequence At A Finite Relaxed-Energy Point
-- statement:
--   This theorem gives a recovery sequence wherever a sequential relaxation is finite.
--
--   Let $X$ be a pseudometric space, let $P$ be a pre-energy, and let $x\in X$. Assume
--
--   $$
--   P.\operatorname{sequentialRelaxation}.\operatorname{FiniteAt}(x),
--   $$
--
--   meaning that the relaxed energy at $x$ is not $\top$. Then there exists an approximating sequence of concrete tests converging to $x$ whose energies converge in the liminf/limsup sense encoded by `HasRecoverySequenceAt`:
--
--   $$
--   P.\operatorname{HasRecoverySequenceAt}
--   \bigl(P.\operatorname{sequentialRelaxation},x\bigr).
--   $$
--
--   The declaration is `hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_readable`. It is a general sequential-relaxation result and assumes neither quadraticity nor a Markov property; finiteness at the point is an explicit hypothesis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.PreEnergy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt {x : X}
--       (hfinite : P.sequentialRelaxation.FiniteAt x) :
--       P.HasRecoverySequenceAt P.sequentialRelaxation x
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Relaxation/Recovery`](https://prove2.me/theorems/61648fda-a4ff-49b1-a631-1c0a917bd957).
--
--   Definition modules: [`Energy/Form/Core`](https://prove2.me/theorems/b744e313-2578-4970-9b76-48a1c977a015), [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Supporting theorems: [`exists_test_near_of_relaxation_lt`](https://prove2.me/theorems/916d7fa1-0ffe-43e9-956d-bd6e80183b18).
--
--   [Source excerpt, lines 34–36](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Relaxation/Recovery.lean#L34-L36) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/Recovery.lean#L29-L84 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.Recovery`, declaration `FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Recovery

universe u
variable {X : Type u} [PseudoMetricSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)

theorem FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_readable {x : X}
    (hfinite : P.sequentialRelaxation.FiniteAt x) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by sorry
