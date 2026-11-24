-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_isotropic_four_iff
-- name    : GlobalTheory.LocalQuad.isotropic_four_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:16:51.332111+00:00
-- url     : https://prove2.me/theorems/e0da7fa7-1359-4812-8f8d-b2f877f6e616
-- title:
--   Local Quad: isotropic four iff
-- statement:
--   The Local Quad construction uses the isotropic four iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuaternaryOfCoordinates.lean#L54-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuaternaryOfCoordinates.lean#L54-L84

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
variable {k : Type*} [Field k]

theorem GlobalTheory.LocalQuad.isotropic_four_iff {a : Fin 4 → k} (ha : a 0 ≠ 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
        x ^ 2 - (-(a 0 * a 1)) * y ^ 2 - (-(a 0 * a 2)) * z ^ 2 + (a 0 * a 3) * t ^ 2 = 0 := by sorry
