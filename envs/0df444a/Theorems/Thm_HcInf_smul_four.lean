-- Prove2me | Theorems.Thm_HcInf_smul_four
-- name    : HcInf.smul_four
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:48.811048+00:00
-- url     : https://prove2.me/theorems/244da4a6-70b9-4be2-b4ed-f4f5ab66a2e9
-- title:
--   Hc Inf: smul four
-- statement:
--   The Hc Inf construction uses the smul four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HasFDerivAtTauR.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HasFDerivAtTauR.lean#L21-L23

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
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem HcInf.smul_four (Z : Mat) : (4 : ℂ) • Z = (1 + 1 + 1 + 1) * Z := by sorry
