-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_twG_mul
-- name    : GlobalTheory.Ex.NumD.twG_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:05.953996+00:00
-- url     : https://prove2.me/theorems/635d22a7-b4fb-469c-b55f-b05ade904ce7
-- title:
--   Num D: tw G mul
-- statement:
--   The Num D construction uses the tw G mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTerms.lean#L73-L82

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

theorem GlobalTheory.Ex.NumD.twG_mul {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) :
    N.twG β u g l hl * N.twG β u g' l' hl' =
      N.twG β u (g * g') (fun z => l z + l' z) (fun a b => by rw [hl, hl']; ring) := by sorry
