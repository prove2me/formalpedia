-- Prove2me | Theorems.Thm_HcInf_nH_eq
-- name    : HcInf.nH_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:28.42629+00:00
-- url     : https://prove2.me/theorems/68626793-9379-4f0c-b9a1-72e9fc691272
-- title:
--   Hc Inf: n H eq
-- statement:
--   The Hc Inf construction uses the n H eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExHua.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExHua.lean#L53-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem HcInf.nH_eq (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q) :
    nH h (x : Mat) = (UpqT.mat (h * cayF P Q x) + 1) * ((1 + 1) - (x : Mat)) := by sorry
