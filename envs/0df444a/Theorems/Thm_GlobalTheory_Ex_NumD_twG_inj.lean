-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_twG_inj
-- name    : GlobalTheory.Ex.NumD.twG_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:06:16.331902+00:00
-- url     : https://prove2.me/theorems/98e50b97-55e1-4697-b3c5-b8a7949b8e8a
-- title:
--   Num D: tw G inj
-- statement:
--   The Num D construction uses the tw G inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L89-L92

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

theorem GlobalTheory.Ex.NumD.twG_inj {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (h : N.twG β u g l hl = N.twG β u g' l hl) : g = g' := by sorry
