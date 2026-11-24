-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedNaturalFiltration_isRightContinuous_of_natRightGerm
-- name    : Kyprianou.Ch03.completedNaturalFiltration_isRightContinuous_of_natRightGerm
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T04:00:18.660359+00:00
-- url     : https://prove2.me/theorems/af0ba35c-4e23-4cfb-ac61-5947d66a2460
-- title:
--   Completed natural filtration is right continuous given the germ inclusion
-- statement:
--   Assume a filtration $\mathcal{F}$ coincides at every time with the $P$-completion of the raw natural filtration $\mathcal{G}_t=\sigma(X_s:s\le t)$ of a process $X$, and that the right germ satisfies $\bigcap_{s>t}\mathcal{G}_s\subseteq\mathcal{G}_t\vee\mathcal{N}$ for every $t$.
--
--   Then $\mathcal{F}$ is right continuous: $\mathcal{F}_{t+}=\mathcal{F}_t$ for all $t$.
--
--   This packages the lattice/identity part of Kyprianou Exercise 3.1 once the Lévy germ inclusion is known.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.1 (packaging step), printed p. 83

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem completedNaturalFiltration_isRightContinuous_of_natRightGerm
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hCompleted : IsCompletedNaturalFiltration P X F)
    (hGerm : forall t : NNReal,
      (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
        PerfCorrMSQ.natFiltr X t ⊔
          MeasurableSpace.generateFrom
            {A : Set Omega |
              exists N : Set Omega,
                MeasurableSet N ∧ P N = 0 ∧ A ⊆ N}) :
    F.IsRightContinuous := by
  sorry

end Kyprianou.Ch03
