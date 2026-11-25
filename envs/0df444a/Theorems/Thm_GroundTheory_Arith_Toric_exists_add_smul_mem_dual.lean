-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_exists_add_smul_mem_dual
-- name    : GroundTheory.Arith.Toric.exists_add_smul_mem_dual
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:24.294808+00:00
-- url     : https://prove2.me/theorems/f726f6eb-897f-4d06-8690-664e09b7a0fe
-- title:
--   Toric: exists add smul mem dual
-- statement:
--   The Toric construction uses the exists add smul mem dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/IsFaceOfIffExistsEqExposedFace.lean#L176-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/IsFaceOfIffExistsEqExposedFace.lean#L176-L194

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

theorem GroundTheory.Arith.Toric.exists_add_smul_mem_dual (S : Finset V) {u w : Dual 𝕜 V}
    (hu : ∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x)
    (hw : ∀ x ∈ exposedFace (hull 𝕜 (S : Set V)) u, 0 ≤ w x) :
    ∃ p : 𝕜, 0 ≤ p ∧ ∀ q : 𝕜, p ≤ q → ∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ w x + q * u x := by sorry
