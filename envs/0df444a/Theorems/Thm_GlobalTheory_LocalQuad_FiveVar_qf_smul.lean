-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_smul
-- name    : GlobalTheory.LocalQuad.FiveVar.qf_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:48.99498+00:00
-- url     : https://prove2.me/theorems/d9418dd9-77b7-43c5-a827-3cf418c5610e
-- title:
--   Five Var: qf smul
-- statement:
--   The Five Var construction uses the qf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L20-L22

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

theorem GlobalTheory.LocalQuad.FiveVar.qf_smul (a x : n → K) (s : K) : qf a (s • x) = s ^ 2 * qf a x := by sorry
