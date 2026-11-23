-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_omegaCx_eq_dot
-- name    : GlobalTheory.LagSplit.omegaCx_eq_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:27.449918+00:00
-- url     : https://prove2.me/theorems/5cbb2326-43c2-482f-9e30-1e8424f88dcf
-- title:
--   Lag Split: omega Cx eq dot
-- statement:
--   The Lag Split construction uses the omega Cx eq dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L47-L49

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

theorem GlobalTheory.LagSplit.omegaCx_eq_dot (a b : Fin g ⊕ Fin g → ℂ) :
    omegaCx g a b = (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (a ∘ Sum.inr) ⬝ᵥ (b ∘ Sum.inl) := by sorry
