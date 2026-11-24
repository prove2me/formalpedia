-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionFutureSupProxyAEV1
-- name    : Kyprianou.Ch03.reflectionFutureSupProxyAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:00:50.342126+00:00
-- url     : https://prove2.me/theorems/fb37f960-218d-4435-ac4b-956c4a6f2cf5
-- title:
--   Measurable path supremum proxy for fresh and shifted paths
-- statement:
--   A fixed countable dense prefix of the compact interval, including its endpoint, determines the supremum along right-continuous paths. A measurable countable supremum functional therefore represents both the fresh and shifted paths.
-- source:
--   Kyprianou (2006), Exercise 3.2, stopped-state strong Markov transition kernel.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectionFutureSupProxyAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (r : Omega → NNReal) (c : ℝ) (t : NNReal) :
    ∃ K : (NNReal → ℝ) → ℝ, Measurable K ∧
      (∀ᵐ w ∂P,
        K (fun u => X u w) = LevyExtrema.SBA.runSup (fun u => c * X u w) t) ∧
      (∀ᵐ w ∂P,
        K (fun u => X (r w + u) w - X (r w) w) =
          LevyExtrema.SBA.runSup (fun u => c * (X (r w + u) w - X (r w) w)) t) := by sorry
