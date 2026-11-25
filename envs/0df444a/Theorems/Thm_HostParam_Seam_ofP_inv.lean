-- Prove2me | Theorems.Thm_HostParam_Seam_ofP_inv
-- name    : HostParam.Seam.ofP_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:30.801251+00:00
-- url     : https://prove2.me/theorems/09bb9439-a0bd-5314-b559-89e94383facc
-- title:
--   Seam: of P inv
-- statement:
--   The Seam construction uses the of P inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L82-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L82-L82

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

theorem HostParam.Seam.ofP_inv (ψ : PChar) : ofP ψ.inv = ⟨(ofP ψ).1, (ofP ψ).2⁻¹⟩ := by sorry
