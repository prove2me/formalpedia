-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Form_exp_count
-- name    : GlobalTheory.Ex.NumD.Form.exp_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:56.301979+00:00
-- url     : https://prove2.me/theorems/b22455d2-a8d3-447d-b06d-2ff3cc57d5dc
-- title:
--   Form: exp count
-- statement:
--   The Form construction uses the exp count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L29-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L29-L49

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

theorem GlobalTheory.Ex.NumD.Form.exp_count {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m) (y χ : N.X) :
    β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) =
      β.be y y / 2 - β.be y y / (m ^ 2 : ℕ) * ((m ^ 2 - 1) / 2 : ℕ) + β.be χ χ / 2 + β.be y χ / (m ^ 2 : ℕ) * m := by sorry
