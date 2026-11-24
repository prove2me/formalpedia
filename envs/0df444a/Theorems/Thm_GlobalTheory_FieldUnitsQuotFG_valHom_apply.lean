-- Prove2me | Theorems.Thm_GlobalTheory_FieldUnitsQuotFG_valHom_apply
-- name    : GlobalTheory.FieldUnitsQuotFG.valHom_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:44.897869+00:00
-- url     : https://prove2.me/theorems/7738322b-699d-4016-a5f9-9922f95dcbc8
-- title:
--   Field Units Quot FG: val Hom apply
-- statement:
--   The Field Units Quot FG construction uses the val Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsFiniteFieldExt.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsFiniteFieldExt.lean#L65-L71

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

theorem GlobalTheory.FieldUnitsQuotFG.valHom_apply [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L]
    (x : Lˣ) (v : HeightOneSpectrum (integralClosure K.O L)) :
    ((valHom K L x v : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.valuation L (x : L) := by sorry
