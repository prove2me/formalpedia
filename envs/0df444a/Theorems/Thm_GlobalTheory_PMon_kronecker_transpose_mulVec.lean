-- Prove2me | Theorems.Thm_GlobalTheory_PMon_kronecker_transpose_mulVec
-- name    : GlobalTheory.PMon.kronecker_transpose_mulVec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:37.435106+00:00
-- url     : https://prove2.me/theorems/9b9672d2-3e06-4a4f-82d8-a1b892a641eb
-- title:
--   PMon: kronecker transpose mul Vec
-- statement:
--   The PMon construction uses the kronecker transpose mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L27-L35

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

theorem GlobalTheory.PMon.kronecker_transpose_mulVec {S : Type*} [CommRing S] (A : Matrix a a S) (C : Matrix b b S) (X : Matrix a b S) :
    (Matrix.kroneckerMap (· * ·) A Cᵀ).mulVec (vecM X) = vecM (A * X * C) := by sorry
