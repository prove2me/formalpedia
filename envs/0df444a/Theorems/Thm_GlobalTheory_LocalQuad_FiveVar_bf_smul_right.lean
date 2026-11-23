-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_smul_right
-- name    : GlobalTheory.LocalQuad.FiveVar.bf_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:42.342619+00:00
-- url     : https://prove2.me/theorems/a5b09dc7-2f51-4e01-8c8c-972b76ab4c01
-- title:
--   Five Var: bf smul right
-- statement:
--   The Five Var construction uses the bf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L28-L30

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

theorem GlobalTheory.LocalQuad.FiveVar.bf_smul_right (a x y : n → K) (s : K) : bf a x (s • y) = s * bf a x y := by sorry
