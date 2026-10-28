-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_exists_test_near_of_relaxation_lt_readable
-- name    : FunctionalInequalities.Energy.PreEnergy.exists_test_near_of_relaxation_lt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:45.212345+00:00
-- url     : https://prove2.me/theorems/916d7fa1-0ffe-43e9-956d-bd6e80183b18
-- title:
--   Concrete Test Below A Strict Relaxed-Energy Bound
-- statement:
--   This is an approximation-selection lemma for sequential relaxation.
--
--   Let $X$ be a pseudometric space, let $P$ be a pre-energy on $X$, let $x\in X$, and let $B\in[0,\infty]$ be an `ENNReal` bound. Assume the relaxed energy is strictly below $B$:
--
--   $$
--   P.\operatorname{sequentialRelaxation}(x)<B.
--   $$
--
--   For every real radius $\varepsilon>0$, there exists a concrete test $f\in P.\operatorname{Test}$ such that
--
--   $$
--   \operatorname{dist}(P.\operatorname{toAmbient}(f),x)<\varepsilon
--   \quad\text{and}\quad
--   (P.\operatorname{energy}(f):\operatorname{ENNReal})<B.
--   $$
--
--   The Lean declaration is `exists_test_near_of_relaxation_lt_readable`. The strict relaxed-energy hypothesis and strict energy conclusion are essential parts of the statement; it does not assert attainment of a minimum.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.PreEnergy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_test_near_of_relaxation_lt {x : X} {bound : ENNReal}
--       (hbound : P.sequentialRelaxation x < bound) {ε : ℝ} (hε : 0 < ε) :
--       ∃ f : P.Test, dist (P.toAmbient f) x < ε ∧ (P.energy f : ENNReal) < bound
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Relaxation/Approximation`](https://prove2.me/theorems/f81a8843-16e0-46de-9ca0-22950d370dd6).
--
--   Definition modules: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   [Source excerpt, lines 31–33](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Relaxation/Approximation.lean#L31-L33) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/Approximation.lean#L29-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.Approximation`, declaration `FunctionalInequalities.Energy.PreEnergy.exists_test_near_of_relaxation_lt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Approximation

universe u
variable {X : Type u} [PseudoMetricSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)

theorem FunctionalInequalities.Energy.PreEnergy.exists_test_near_of_relaxation_lt_readable {x : X} {bound : ENNReal}
    (hbound : P.sequentialRelaxation x < bound) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : P.Test, dist (P.toAmbient f) x < ε ∧ (P.energy f : ENNReal) < bound := by sorry
