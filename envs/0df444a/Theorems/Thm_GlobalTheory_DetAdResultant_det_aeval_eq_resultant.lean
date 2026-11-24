-- Prove2me | Theorems.Thm_GlobalTheory_DetAdResultant_det_aeval_eq_resultant
-- name    : GlobalTheory.DetAdResultant.det_aeval_eq_resultant
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:25.589635+00:00
-- url     : https://prove2.me/theorems/86dee1a7-c56e-4770-b322-c7b518c3bdee
-- title:
--   Det Ad Resultant: det aeval eq resultant
-- statement:
--   The Det Ad Resultant construction uses the det aeval eq resultant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetCommutatorMapEqCharpolyResultant.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetCommutatorMapEqCharpolyResultant.lean#L25-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
open GlobalTheory GlobalTheory.DetAdResultant

theorem GlobalTheory.DetAdResultant.det_aeval_eq_resultant {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι E) (g : E[X]) (hg : g.Monic) :
    (aeval A g).det = resultant A.charpoly g := by sorry
