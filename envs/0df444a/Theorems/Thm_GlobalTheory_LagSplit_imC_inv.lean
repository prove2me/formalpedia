-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_imC_inv
-- name    : GlobalTheory.LagSplit.imC_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:17.38575+00:00
-- url     : https://prove2.me/theorems/8f7d71fa-b305-4fb1-a4c8-b518d5aeaacf
-- title:
--   Lag Split: im C inv
-- statement:
--   The Lag Split construction uses the im C inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L127-L129

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

theorem GlobalTheory.LagSplit.imC_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    (imC τ)⁻¹ = ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) := by sorry
