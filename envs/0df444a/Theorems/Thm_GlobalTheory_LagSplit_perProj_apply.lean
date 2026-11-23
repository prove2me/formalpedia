-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_perProj_apply
-- name    : GlobalTheory.LagSplit.perProj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:41.10132+00:00
-- url     : https://prove2.me/theorems/77efe67f-9d8e-4b21-adf3-7ea43c64048e
-- title:
--   Lag Split: per Proj apply
-- statement:
--   The Lag Split construction uses the per Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L80-L81

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

theorem GlobalTheory.LagSplit.perProj_apply (τ : Matrix (Fin g) (Fin g) ℂ) (u : Fin g ⊕ Fin g → ℂ) :
    perProj τ u = u ∘ Sum.inl + τ *ᵥ (u ∘ Sum.inr) := by sorry
