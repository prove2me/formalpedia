-- Prove2me | Theorems.Thm_GlobalTheory_pow_mul_le_comap_pow
-- name    : GlobalTheory.pow_mul_le_comap_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:55.712228+00:00
-- url     : https://prove2.me/theorems/f634f0c6-0e43-49c1-8432-e07899b3db50
-- title:
--   Global Theory: pow mul le comap pow
-- statement:
--   The Global Theory construction uses the pow mul le comap pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L23-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]

theorem GlobalTheory.pow_mul_le_comap_pow (φ : A →+* R) {J : Ideal A} {I : Ideal R} {k : ℕ}
    (hk : J.map φ ^ k ≤ I) (n : ℕ) : J ^ (k * n) ≤ (I ^ n).comap φ := by sorry
