-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_add_left
-- name    : GlobalTheory.LocalQuad.FiveVar.bf_add_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:13:49.604707+00:00
-- url     : https://prove2.me/theorems/9745a7f3-3603-4e9c-97dd-51b52efce5d8
-- title:
--   Five Var: bf add left
-- statement:
--   The Five Var construction uses the bf add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L32-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]

theorem GlobalTheory.LocalQuad.FiveVar.bf_add_left (a x y z : n → K) : bf a (x + y) z = bf a x z + bf a y z := by sorry
