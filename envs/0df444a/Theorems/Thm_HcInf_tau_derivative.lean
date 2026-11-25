-- Prove2me | Theorems.Thm_HcInf_tau_derivative
-- name    : HcInf.tau_derivative
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:33.581619+00:00
-- url     : https://prove2.me/theorems/4969e5a7-7e1f-5fc6-a969-b1c578bc9353
-- title:
--   Hc Inf: tau derivative
-- statement:
--   The Hc Inf construction uses the tau derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HasFDerivAtTauR.lean#L137-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HasFDerivAtTauR.lean#L137-L137

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HasFDerivAtTauR
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
open HcS.BasicNotions Matrix Filter Topology
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem HcInf.tau_derivative : TauDeriv := by sorry
