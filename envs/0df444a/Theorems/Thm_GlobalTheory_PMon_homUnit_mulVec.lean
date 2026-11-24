-- Prove2me | Theorems.Thm_GlobalTheory_PMon_homUnit_mulVec
-- name    : GlobalTheory.PMon.homUnit_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:43.456989+00:00
-- url     : https://prove2.me/theorems/f1caea18-6133-4cb4-8ac9-49d8c6e66357
-- title:
--   PMon: hom Unit mul Vec
-- statement:
--   The PMon construction uses the hom Unit mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L37-L43

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

theorem GlobalTheory.PMon.homUnit_mulVec {S : Type*} [CommRing S] (f : R →+* S) (A : GL a R) (B : GL b R) (X : Matrix a b S) :
    (((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R).map f).mulVec (vecM X) =
      vecM ((A : Matrix a a R).map f * X * ((B⁻¹ : GL b R) : Matrix b b R).map f) := by sorry
