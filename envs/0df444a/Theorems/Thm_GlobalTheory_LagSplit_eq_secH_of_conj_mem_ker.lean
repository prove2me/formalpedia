-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_eq_secH_of_conj_mem_ker
-- name    : GlobalTheory.LagSplit.eq_secH_of_conj_mem_ker
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:54.98807+00:00
-- url     : https://prove2.me/theorems/796f9a8d-390f-47bb-aaa3-5b5c905a5a61
-- title:
--   Lag Split: eq sec H of conj mem ker
-- statement:
--   The Lag Split construction uses the eq sec H of conj mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L174-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L174-L179

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

theorem GlobalTheory.LagSplit.eq_secH_of_conj_mem_ker {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    {u : Fin g ⊕ Fin g → ℂ} {z : Fin g → ℂ} (hu : perProj τ u = z) (hc : perProj τ (star u) = 0) :
    u = secH τ z := by sorry
