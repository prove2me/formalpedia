-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_omegaCx_intCast
-- name    : GlobalTheory.LagSplit.omegaCx_intCast
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:11.821209+00:00
-- url     : https://prove2.me/theorems/b01f74f4-062e-4107-adc2-120e85cc392a
-- title:
--   Lag Split: omega Cx int Cast
-- statement:
--   The Lag Split construction uses the omega Cx int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L55-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}

theorem GlobalTheory.LagSplit.omegaCx_intCast (a b : Fin g ⊕ Fin g → ℤ) :
    omegaCx g (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (omegaStd a b : ℂ) := by sorry
