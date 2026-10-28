-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_lowerSemicontinuous_sequentialRelaxation_readable
-- name    : FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:42.419844+00:00
-- url     : https://prove2.me/theorems/17428d33-0be2-4fb1-81de-28e6c75ce12e
-- title:
--   Lower Semicontinuity Of Sequential Relaxation
-- statement:
--   This theorem states that sequential relaxation is lower semicontinuous in a pseudometric ambient space.
--
--   Let $X$ be a pseudometric space and let $P$ be any pre-energy on $X$. Then the function assigning to $x\in X$ the `ENNReal`-valued sequentially relaxed energy is lower semicontinuous:
--
--   $$
--   \operatorname{LowerSemicontinuous}\!\left(
--    x\mapsto P.\operatorname{sequentialRelaxation}(x)
--   \right).
--   $$
--
--   The declaration is `lowerSemicontinuous_sequentialRelaxation_readable`. The conclusion allows relaxed energy equal to $\top$ and does not require a dense realization, quadratic structure, closability, or a Markov property.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.PreEnergy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lowerSemicontinuous_sequentialRelaxation :
--       LowerSemicontinuous (fun x ↦ P.sequentialRelaxation x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Relaxation/LowerSemicontinuous`](https://prove2.me/theorems/212961e9-bab7-4abf-a6d1-368cc11f24f3).
--
--   Definition modules: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Supporting theorems: [`exists_test_near_of_relaxation_lt`](https://prove2.me/theorems/916d7fa1-0ffe-43e9-956d-bd6e80183b18).
--
--   [Source excerpt, lines 32–33](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Relaxation/LowerSemicontinuous.lean#L32-L33) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LowerSemicontinuous.lean#L31-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous`, declaration `FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LowerSemicontinuous

universe u
variable {X : Type u} [PseudoMetricSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)

theorem FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation_readable :
    LowerSemicontinuous (fun x ↦ P.sequentialRelaxation x) := by sorry
