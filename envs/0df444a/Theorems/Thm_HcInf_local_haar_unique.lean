-- Prove2me | Theorems.Thm_HcInf_local_haar_unique
-- name    : HcInf.local_haar_unique
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:24.806908+00:00
-- url     : https://prove2.me/theorems/e0365390-ed95-4e18-8e3f-811bbcf9f4af
-- title:
--   Hc Inf: local haar unique
-- statement:
--   The Hc Inf construction uses the local haar unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExLHU.lean#L97-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExLHU.lean#L97-L152

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExLHU
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
open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem HcInf.local_haar_unique : LocalHaarUnique := by sorry
