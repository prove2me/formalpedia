-- Prove2me | Theorems.Thm_GlobalTheory_FieldUnitsQuotFG_finite_spec
-- name    : GlobalTheory.FieldUnitsQuotFG.finite_spec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:44.732798+00:00
-- url     : https://prove2.me/theorems/ddd1d925-fe61-456d-8a5f-9b0289b6d748
-- title:
--   Field Units Quot FG: finite spec
-- statement:
--   The Field Units Quot FG construction uses the finite spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsFiniteFieldExt.lean#L29-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsFiniteFieldExt.lean#L29-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.FieldUnitsQuotFG
variable (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
  [FiniteDimensional K.E L]

theorem GlobalTheory.FieldUnitsQuotFG.finite_spec [IsDedekindDomain (integralClosure K.O L)] :
    Finite (HeightOneSpectrum (integralClosure K.O L)) := by sorry
