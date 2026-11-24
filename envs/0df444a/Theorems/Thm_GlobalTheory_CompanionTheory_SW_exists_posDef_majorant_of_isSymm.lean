-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_exists_posDef_majorant_of_isSymm
-- name    : GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:32.385136+00:00
-- url     : https://prove2.me/theorems/ba13bc35-62dd-453e-97f2-5ef729e79011
-- title:
--   SW: exists pos Def majorant of is Symm
-- statement:
--   The SW construction uses the exists pos Def majorant of is Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SymmetricInvertibleExistsPosdefCongruence.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SymmetricInvertibleExistsPosdefCongruence.lean#L7-L51

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SymmetricInvertibleExistsPosdefCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 →
      ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by sorry
