-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_add
-- name    : GlobalTheory.LocalQuad.FiveVar.qf_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:44.723317+00:00
-- url     : https://prove2.me/theorems/a388ae9a-5fb9-4994-ad68-1e6ef1dec9f0
-- title:
--   Five Var: qf add
-- statement:
--   The Five Var construction uses the qf add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L16-L18

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

theorem GlobalTheory.LocalQuad.FiveVar.qf_add (a x y : n → K) : qf a (x + y) = qf a x + bf a x y + qf a y := by sorry
