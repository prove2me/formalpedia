-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_eq_omegaCx_of_intCast
-- name    : GlobalTheory.LagSplit.eq_omegaCx_of_intCast
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:24.30692+00:00
-- url     : https://prove2.me/theorems/4799c0b7-ae1e-5c61-9e42-7e4917b2bf29
-- title:
--   Lag Split: eq omega Cx of int Cast
-- statement:
--   The Lag Split construction uses the eq omega Cx of int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L59-L67

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

theorem GlobalTheory.LagSplit.eq_omegaCx_of_intCast (B : LinearMap.BilinForm ℂ (Fin g ⊕ Fin g → ℂ))
    (hB : ∀ a b : Fin g ⊕ Fin g → ℤ,
      B (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (omegaStd a b : ℂ)) : B = omegaCx g := by sorry
