-- Prove2me | Theorems.Thm_GlobalTheory_ResRect_sidesIn_compl
-- name    : GlobalTheory.ResRect.sidesIn_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:14.183395+00:00
-- url     : https://prove2.me/theorems/8a289e71-6836-4da5-a20c-aba04c00b055
-- title:
--   Res Rect: sides In compl
-- statement:
--   The Res Rect construction uses the sides In compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L90-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect

theorem GlobalTheory.ResRect.sidesIn_compl {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) : SidesIn a b c d {p}ᶜ := by sorry
