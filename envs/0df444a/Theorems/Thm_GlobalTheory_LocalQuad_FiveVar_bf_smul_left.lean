-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_smul_left
-- name    : GlobalTheory.LocalQuad.FiveVar.bf_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:35.144688+00:00
-- url     : https://prove2.me/theorems/05500f45-c9a0-45ba-ae67-c493a168358c
-- title:
--   Five Var: bf smul left
-- statement:
--   The Five Var construction uses the bf smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L24-L26

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

theorem GlobalTheory.LocalQuad.FiveVar.bf_smul_left (a x y : n → K) (s : K) : bf a (s • x) y = s * bf a x y := by sorry
