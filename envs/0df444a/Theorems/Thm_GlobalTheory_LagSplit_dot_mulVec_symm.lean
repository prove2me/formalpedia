-- Prove2me | Theorems.Thm_GlobalTheory_LagSplit_dot_mulVec_symm
-- name    : GlobalTheory.LagSplit.dot_mulVec_symm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:12.532446+00:00
-- url     : https://prove2.me/theorems/8c922542-8e8b-429f-ad61-d8acc08f8e5d
-- title:
--   Lag Split: dot mul Vec symm
-- statement:
--   The Lag Split construction uses the dot mul Vec symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L102-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm

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

theorem GlobalTheory.LagSplit.dot_mulVec_symm {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.IsSymm) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := by sorry
