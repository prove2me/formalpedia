-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_aff_low
-- name    : GlobalTheory.LatClass.aff_low
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:41.978268+00:00
-- url     : https://prove2.me/theorems/1456f34b-e5c6-4361-9c3e-f5d5117a019c
-- title:
--   Lat Class: aff low
-- statement:
--   The Lat Class construction uses the aff low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L13-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [DecidableEq n']

theorem GlobalTheory.LatClass.aff_low (x₀ : Matrix n n' k) (y) (w : n' → k) (s : k) :
    affPt (c := c + 1) 1 x₀ y *ᵥ Sum.elim w (Pi.single 0 s) = Sum.elim (x₀ *ᵥ w) (Pi.single 0 s) := by sorry
