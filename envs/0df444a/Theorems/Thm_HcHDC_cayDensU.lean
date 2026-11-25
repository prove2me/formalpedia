-- Prove2me | Theorems.Thm_HcHDC_cayDensU
-- name    : HcHDC.cayDensU
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:14.133798+00:00
-- url     : https://prove2.me/theorems/2a620dea-7aa1-439d-bd6e-2e83b96abaa8
-- title:
--   Hc HDC: cay Dens U
-- statement:
--   The Hc HDC construction uses the cay Dens U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExHaar.lean#L14-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExHaar.lean#L14-L151

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PreimageSubsetImage
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HuaInvOfTauDeriv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HasFDerivAtTauR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExLHU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcHDC
open HcInf HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem HcHDC.cayDensU (P Q : ℕ) (m : Measure (UpqT P Q)) [hm : m.IsHaarMeasure] (lam : Measure (lieU P Q))
    [hlam : lam.IsAddHaarMeasure] :
    ∃ D ∈ 𝓝 (0 : lieU P Q), MeasurableSet D ∧ ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧ ContinuousAt f 0 ∧
      f 0 ≠ 0 ∧ f 0 ≠ ⊤ ∧ (m.restrict (cayS D)).map (cayInv P Q) = (lam.restrict D).withDensity f := by sorry
