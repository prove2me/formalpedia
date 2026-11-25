-- Prove2me | Theorems.Thm_HostParam_Seam_ofP_of
-- name    : HostParam.Seam.ofP_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:01.657025+00:00
-- url     : https://prove2.me/theorems/f5ee729b-27b2-47ce-a031-edaedc025d9a
-- title:
--   Seam: of P of
-- statement:
--   The Seam construction uses the of P of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L78-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L78-L78

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

theorem HostParam.Seam.ofP_of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ofP (PChar.of χ) = prim χ := by sorry
