-- Prove2me | Theorems.Thm_HcInf_cayley_domain_eq
-- name    : HcInf.cayley_domain_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:14:57.081494+00:00
-- url     : https://prove2.me/theorems/964a4527-282d-4bba-be96-509d7dfd3150
-- title:
--   Hc Inf: cayley domain eq
-- statement:
--   The Hc Inf construction uses the cayley domain eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L177-L183

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

theorem HcInf.cayley_domain_eq : cayS (D0 P Q) = {g : UpqT P Q | IsUnit (UpqT.mat g + 1).det} := by sorry
