-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeft_stoppingSequenceLimit
-- name    : Kyprianou.Ch03.quasiLeft_stoppingSequenceLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T14:57:18.614912+00:00
-- url     : https://prove2.me/theorems/e40f7821-bc5b-415b-9859-f876418451d9
-- title:
--   Lemma 3.2 source clause 1
-- statement:
--   Exact independently quantified clause 1 of Lemma 3.2. All original hypotheses and process domains are retained.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Lemma 3.2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem quasiLeft_stoppingSequenceLimit
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega -> WithTop NNReal)
    (Tn : Nat -> Omega -> WithTop NNReal)
    (timeT : Omega -> NNReal) (timeTn : Nat -> Omega -> NNReal)
    (hTimeT : forall omega, T omega != ⊤ ->
      T omega = (timeT omega : WithTop NNReal))
    (hTimeTn : forall n omega, Tn n omega != ⊤ ->
      Tn n omega = (timeTn n omega : WithTop NNReal))
    (hT : IsStoppingTime F T)
    (hTn : forall n, IsStoppingTime F (Tn n))
    (hIncreasing : ∀ᵐ omega : Omega ∂ P,
      Monotone (fun n => Tn n omega))
    (hLimit : ∀ᵐ omega : Omega ∂ P,
      Tendsto (fun n => Tn n omega) atTop (nhds (T omega))) :
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      Tendsto (fun n => X (timeTn n omega) omega)
        atTop (nhds (X (timeT omega) omega))) := by
  sorry

end Kyprianou.Ch03
