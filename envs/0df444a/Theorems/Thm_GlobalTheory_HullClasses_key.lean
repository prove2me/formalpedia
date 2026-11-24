-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_key
-- name    : GlobalTheory.HullClasses.key
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:36:33.080942+00:00
-- url     : https://prove2.me/theorems/60f1076b-7ef5-4fc1-b739-09ebca2b7aff
-- title:
--   Hull Classes: key
-- statement:
--   The Hull Classes construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L75-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L75-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.HullClasses.key (x : B.A) (c cb : K.O) (hc : B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb) (a b : B.Aˣ)
    (h4 : ∀ y ∈ mulLat K.O (a : B.A) (abelian₂ B), ∀ z ∈ mulLat K.O (a : B.A) (abelian₂ B),
      B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range)
    (h3 : ∀ y, (∀ z ∈ mulLat K.O (b : B.A) (abelian₂ B), B.herm x y z ∈ (algebraMap K.O K.E).range) →
      y ∈ mulLat K.O (b : B.A) (abelian₂ B)) :
    mulLat K.O (algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a)) (abelian₂ B) ≤
      mulLat K.O ((b : B.A) * B.σ b) (abelian₂ B) := by sorry
