-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCharMult_half_mulVec
-- name    : GlobalTheory.ThetaCharMult.half_mulVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:48.673379+00:00
-- url     : https://prove2.me/theorems/bf96b258-b5d8-48ca-911b-25ee2a2468bb
-- title:
--   Theta Char Mult: half mul Vec
-- statement:
--   The Theta Char Mult construction uses the half mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L118-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L118-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaCharMult
variable {g : ℕ}

theorem GlobalTheory.ThetaCharMult.half_mulVec (M : Matrix (Fin g) (Fin g) ℤ) (N : Matrix (Fin g) (Fin g) ℤ)
    (n n' : Fin g → ℤ) :
    ofRealVec (halfVec (M *ᵥ n + N *ᵥ n')) =
      M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n) +
        N.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n') := by sorry
