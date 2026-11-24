-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChange_swap_mem_symplectic
-- name    : GlobalTheory.PeriodChange.swap_mem_symplectic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:49.219381+00:00
-- url     : https://prove2.me/theorems/2cb1e8fe-9501-4be5-b62d-1b7f70cd9ba3
-- title:
--   Period Change: swap mem symplectic
-- statement:
--   The Period Change construction uses the swap mem symplectic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ChangeOfNormalisation.lean#L32-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ChangeOfNormalisation.lean#L32-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ChangeOfNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChange
open Complex Matrix NumberField

theorem GlobalTheory.PeriodChange.swap_mem_symplectic {g : ℕ} (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hN : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd (N *ᵥ a) (N *ᵥ b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) :
    Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∈
      Matrix.symplecticGroup (Fin g) ℤ := by sorry
