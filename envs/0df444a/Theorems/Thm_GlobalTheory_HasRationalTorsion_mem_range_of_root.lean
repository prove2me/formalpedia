-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_mem_range_of_root
-- name    : GlobalTheory.HasRationalTorsion.mem_range_of_root
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:08.701649+00:00
-- url     : https://prove2.me/theorems/6c4e8069-6d33-4938-ab73-d4f892fdc5f1
-- title:
--   Has Rational Torsion: mem range of root
-- statement:
--   The Has Rational Torsion construction uses the mem range of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L231-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L231-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
omit [CharZero K] [IsAlgClosed L]

theorem GlobalTheory.HasRationalTorsion.mem_range_of_root (h : HasRationalTorsion W L 2) (h₁ : W.a₁ = 0)
    (h₃ : W.a₃ = 0) {x : L} (hx : x ^ 3 + algebraMap K L W.a₂ * x ^ 2 + algebraMap K L W.a₄ * x
      + algebraMap K L W.a₆ = 0) : x ∈ (algebraMap K L).range := by sorry
