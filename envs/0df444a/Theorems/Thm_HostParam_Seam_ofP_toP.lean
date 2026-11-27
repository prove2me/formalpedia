-- Prove2me | Theorems.Thm_HostParam_Seam_ofP_toP
-- name    : HostParam.Seam.ofP_toP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:48.516678+00:00
-- url     : https://prove2.me/theorems/a9047d81-908f-48ff-bed9-44e8f036826a
-- title:
--   Seam: of P to P
-- statement:
--   The Seam construction uses the of P to P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L61-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L61-L61

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_OfPInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC Formalism.FrobeniusOrbits
noncomputable section
open HostParam HostParam.Seam

theorem HostParam.Seam.ofP_toP (κ : PrimChar) (h : 0 < κ.1) (hp : κ.2.IsPrimitive) : ofP (toP κ h hp) = κ := by sorry
