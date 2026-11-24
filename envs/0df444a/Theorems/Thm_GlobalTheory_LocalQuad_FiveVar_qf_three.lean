-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_three
-- name    : GlobalTheory.LocalQuad.FiveVar.qf_three
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:13:49.915417+00:00
-- url     : https://prove2.me/theorems/6f2c91dc-3ed3-49ab-8e9d-08e2655415e7
-- title:
--   Five Var: qf three
-- statement:
--   The Five Var construction uses the qf three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L40-L46

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

theorem GlobalTheory.LocalQuad.FiveVar.qf_three (a p q r : n → K) (x : Fin 3 → K) (w : K) :
    qf a (x 0 • p + x 1 • q + x 2 • r) / w = ∑ i, ∑ j,
      (![![qf a p / w, bf a p q / w, bf a p r / w], ![0, qf a q / w, bf a q r / w],
        ![0, 0, qf a r / w]] : Fin 3 → Fin 3 → K) i j * x i * x j := by sorry
