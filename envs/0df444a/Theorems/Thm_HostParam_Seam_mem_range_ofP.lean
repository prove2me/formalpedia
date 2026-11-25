-- Prove2me | Theorems.Thm_HostParam_Seam_mem_range_ofP
-- name    : HostParam.Seam.mem_range_ofP
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:10.46589+00:00
-- url     : https://prove2.me/theorems/afd97170-371e-5d8b-868d-b491a6b0b81a
-- title:
--   Seam: mem range of P
-- statement:
--   The Seam construction uses the mem range of P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L75-L76

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

theorem HostParam.Seam.mem_range_ofP (κ : PrimChar) : κ ∈ Set.range ofP ↔ 0 < κ.1 ∧ κ.2.IsPrimitive := by sorry
