-- Prove2me | Theorems.Thm_HcInf_cayF_mat
-- name    : HcInf.cayF_mat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:01.405356+00:00
-- url     : https://prove2.me/theorems/68c3300d-7110-5518-9d7f-629f005611f4
-- title:
--   Hc Inf: cay F mat
-- statement:
--   The Hc Inf construction uses the cay F mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L115-L118

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

theorem HcInf.cayF_mat (X : lieU P Q) (hX : X ∈ D0 P Q) :
    UpqT.mat (cayF P Q X) = ((1 + 1) + ((X : lieU P Q) : Mat)) * ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by sorry
