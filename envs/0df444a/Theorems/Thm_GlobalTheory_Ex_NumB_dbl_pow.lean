-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumB_dbl_pow
-- name    : GlobalTheory.Ex.NumB.dbl_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:13.537897+00:00
-- url     : https://prove2.me/theorems/58f96378-c2ba-4624-a4f2-72cb9b5286f3
-- title:
--   Num B: dbl pow
-- statement:
--   The Num B construction uses the dbl pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L93-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L93-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
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
open GlobalTheory.Ex.NumB
variable {O : Type} [CommRing O] (B : NumB O)

theorem GlobalTheory.Ex.NumB.dbl_pow (a : ℕ) (x : B.A) :
    dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) =
      dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 := by sorry
