-- Prove2me | Theorems.Thm_HcInf_mem_cayley_domain_of
-- name    : HcInf.mem_cayley_domain_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:01.591971+00:00
-- url     : https://prove2.me/theorems/1b5864fe-d159-4158-b83e-26317a74b48e
-- title:
--   Hc Inf: mem cayley domain of
-- statement:
--   The Hc Inf construction uses the mem cayley domain of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L92-L95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
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
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem HcInf.mem_cayley_domain_of (g : UpqT P Q) (X : lieU P Q)
    (h : UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) = (1 + 1) + ((X : lieU P Q) : Mat)) :
    X ∈ D0 P Q := by sorry
