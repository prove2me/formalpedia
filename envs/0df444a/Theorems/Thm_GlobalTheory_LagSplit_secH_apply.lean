-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_secH_apply
-- name    : GlobalTheory.LagSplit.secH_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:14.559814+00:00
-- url     : https://prove2.me/theorems/508c0b27-ae86-40ff-942b-2103c1cf113e
-- title:
--   Lag Split: sec H apply
-- statement:
--   The Lag Split construction uses the sec H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L99-L100

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

theorem GlobalTheory.LagSplit.secH_apply (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : secH τ z =
    Sum.elim (-(τ.map star *ᵥ (((2 * I) • imC τ)⁻¹ *ᵥ z))) (((2 * I) • imC τ)⁻¹ *ᵥ z) := by sorry
