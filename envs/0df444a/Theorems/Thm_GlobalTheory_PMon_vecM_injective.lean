-- Prove2me | Theorems.Thm_GlobalTheory_PMon_vecM_injective
-- name    : GlobalTheory.PMon.vecM_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:39:01.513516+00:00
-- url     : https://prove2.me/theorems/35cb793e-667c-439c-84e7-fc7247547af1
-- title:
--   PMon: vec M injective
-- statement:
--   The PMon construction uses the vec M injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L61-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PMon
variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem GlobalTheory.PMon.vecM_injective {S : Type*} : Function.Injective (vecM : Matrix a b S → a × b → S) := by sorry
