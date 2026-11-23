-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Form_div_add_left
-- name    : GlobalTheory.Ex.NumD.Form.div_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:16.151807+00:00
-- url     : https://prove2.me/theorems/2d7e32d0-8889-4310-bb27-319cebb04142
-- title:
--   Form: div add left
-- statement:
--   The Form construction uses the div add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
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
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.Ex.NumD.Form.div_add_left {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + y) z / j = β.be x z / j + β.be y z / j := by sorry
