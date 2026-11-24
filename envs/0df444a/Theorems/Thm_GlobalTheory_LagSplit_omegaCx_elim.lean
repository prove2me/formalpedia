-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_omegaCx_elim
-- name    : GlobalTheory.LagSplit.omegaCx_elim
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:53.825244+00:00
-- url     : https://prove2.me/theorems/e4f32b6d-e2fa-4e93-97f3-1adbd3210144
-- title:
--   Lag Split: omega Cx elim
-- statement:
--   The Lag Split construction uses the omega Cx elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L51-L53

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

theorem GlobalTheory.LagSplit.omegaCx_elim (m n m' n' : Fin g → ℂ) :
    omegaCx g (Sum.elim m n) (Sum.elim m' n') = m ⬝ᵥ n' - n ⬝ᵥ m' := by sorry
