-- Prove2me | Theorems.Thm_GlobalTheory_WittGauss_map_scaleCoeff
-- name    : GlobalTheory.WittGauss.map_scaleCoeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:12:19.382011+00:00
-- url     : https://prove2.me/theorems/a2ca1347-3290-4974-ae49-db613da83dc6
-- title:
--   Witt Gauss: map scale Coeff
-- statement:
--   The Witt Gauss construction uses the map scale Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector

theorem GlobalTheory.WittGauss.map_scaleCoeff (p : ℕ) [Fact p.Prime] {S S' : Type} [CommRing S] [CommRing S']
    (f : S →+* S') (t : S) (x : WittVector p S) :
    WittVector.map f (scaleCoeff p t x) = scaleCoeff p (f t) (WittVector.map f x) := by sorry
