-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumB_dbl_mul
-- name    : GlobalTheory.Ex.NumB.dbl_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:12.179955+00:00
-- url     : https://prove2.me/theorems/a76f99bc-b887-426e-a6ae-30017980fc6e
-- title:
--   Num B: dbl mul
-- statement:
--   The Num B construction uses the dbl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L76-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L76-L91

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

theorem GlobalTheory.Ex.NumB.dbl_mul (x y : B.A) :
    dbl B.θ B.σ (x * y) * (B.θ (x * y) x y * B.θ x x y * B.θ y x y) =
      dbl B.θ B.σ x * dbl B.θ B.σ y := by sorry
