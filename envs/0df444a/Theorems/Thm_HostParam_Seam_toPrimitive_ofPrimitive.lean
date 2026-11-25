-- Prove2me | Theorems.Thm_HostParam_Seam_toPrimitive_ofPrimitive
-- name    : HostParam.Seam.toPrimitive_ofPrimitive
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:17.237655+00:00
-- url     : https://prove2.me/theorems/64d5dab8-10d7-4322-86ce-9e6513a4d8e4
-- title:
--   Seam: to Primitive of Primitive
-- statement:
--   The Seam construction uses the to Primitive of Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L67-L67

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

theorem HostParam.Seam.toPrimitive_ofPrimitive (ψ : PChar) : toP (ofP ψ) (ofP_fst_pos ψ) (ofP_snd_isPrimitive ψ) = ψ := by sorry
