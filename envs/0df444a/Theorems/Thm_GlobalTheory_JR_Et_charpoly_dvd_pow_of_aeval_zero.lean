-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_charpoly_dvd_pow_of_aeval_zero
-- name    : GlobalTheory.JR.Et.charpoly_dvd_pow_of_aeval_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:36.817795+00:00
-- url     : https://prove2.me/theorems/9c52a453-fc4e-4bfd-a023-be89941efd4f
-- title:
--   Et: charpoly dvd pow of aeval zero
-- statement:
--   The Et construction uses the charpoly dvd pow of aeval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSubringEqOK.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSubringEqOK.lean#L11-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et

theorem GlobalTheory.JR.Et.charpoly_dvd_pow_of_aeval_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by sorry
