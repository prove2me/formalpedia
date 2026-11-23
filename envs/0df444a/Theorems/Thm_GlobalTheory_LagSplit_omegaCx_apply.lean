-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_omegaCx_apply
-- name    : GlobalTheory.LagSplit.omegaCx_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:34.66368+00:00
-- url     : https://prove2.me/theorems/545f573d-9038-450a-a613-9c10361828de
-- title:
--   Lag Split: omega Cx apply
-- statement:
--   The Lag Split construction uses the omega Cx apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L44-L45

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

theorem GlobalTheory.LagSplit.omegaCx_apply (a b : Fin g ⊕ Fin g → ℂ) :
    omegaCx g a b = ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)) := by sorry
