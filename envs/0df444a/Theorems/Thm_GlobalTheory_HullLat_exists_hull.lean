-- Prove2me | Theorems.Thm_GlobalTheory_HullLat_exists_hull
-- name    : GlobalTheory.HullLat.exists_hull
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:39.030064+00:00
-- url     : https://prove2.me/theorems/8a536847-9d06-40af-bc94-fd50e477540f
-- title:
--   Hull Lat: exists hull
-- statement:
--   The Hull Lat construction uses the exists hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMaximalOrderHullSelfDualStableLattice.lean#L14-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMaximalOrderHullSelfDualStableLattice.lean#L14-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMaximalOrderHullSelfDualStableLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.HullLat

theorem GlobalTheory.HullLat.exists_hull : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (c : K.O), c ≠ 0 → ∀ L ∈ B.X x,
    (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) →
    ∃ J : Submodule K.O B.A, IsLat K.O K.E J ∧ (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) ∧
      (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) ∧
      (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
        (algebraMap K.O K.E).range) ∧ mulLat K.O (algebraMap K.O B.A c) J ≤ L ∧ L ≤ J := by sorry
