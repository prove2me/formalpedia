-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_isotropic_succ_iff
-- name    : GlobalTheory.LocalQuad.isotropic_succ_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:26.665055+00:00
-- url     : https://prove2.me/theorems/9320dcf7-56d7-443d-a8f6-4fb45a94525d
-- title:
--   Local Quad: isotropic succ iff
-- statement:
--   The Local Quad construction uses the isotropic succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuaternaryOfCoordinates.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuaternaryOfCoordinates.lean#L86-L103

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

theorem GlobalTheory.LocalQuad.isotropic_succ_iff {n : ℕ} {a : Fin (n + 1) → k} :
    (∃ x : Fin (n + 1) → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ (t : k) (z : Fin n → k), (t ≠ 0 ∨ z ≠ 0) ∧ a 0 * t ^ 2 + ∑ i, a i.succ * z i ^ 2 = 0 := by sorry
