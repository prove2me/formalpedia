-- Prove2me | Theorems.Thm_GlobalTheory_Ex_SymLift_odd_root_iff
-- name    : GlobalTheory.Ex.SymLift.odd_root_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:05:25.612212+00:00
-- url     : https://prove2.me/theorems/3d72948f-a455-4711-a630-8bd214edd606
-- title:
--   Sym Lift: odd root iff
-- statement:
--   The Sym Lift construction uses the odd root iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L11-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift

theorem GlobalTheory.Ex.SymLift.odd_root_iff {U : Type} [CommGroup U] (j : ℕ) (E P w : U) (h : E ^ (2 * j + 1) = P ^ 2) :
    w = P / E ^ j ↔ (w ^ 2 = E ∧ w ^ (2 * j + 1) = P) := by sorry
