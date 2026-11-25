-- Prove2me | Theorems.Thm_GlobalTheory_Klein_DiffUnit_disc_eq
-- name    : GlobalTheory.Klein.DiffUnit.disc_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:34.877741+00:00
-- url     : https://prove2.me/theorems/dce8366c-e64d-4576-977b-cee373b3a012
-- title:
--   Diff Unit: disc eq
-- statement:
--   The Diff Unit construction uses the disc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormWeierstrassPSubEqOne.lean#L36-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormWeierstrassPSubEqOne.lean#L36-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein GlobalTheory.Klein.DiffUnit
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.Klein.DiffUnit.disc_eq {K : Type*} [Field K] (h r g₂ g₃ P Q y z s t : K) (hh : 2 * h = 1) (hD : P - Q ≠ 0)
    (hy : y ^ 2 = 4 * P ^ 3 - g₂ * P - g₃) (hz : z ^ 2 = 4 * Q ^ 3 - g₂ * Q - g₃)
    (hs : s * (P - Q) = y - z) (ht : t * (P - Q) = y + z) :
    ∃ A B C : K, A = 12 * (P - r) + 12 * r ∧
      B = s * t + (4 * ((Q - r) + 2 * (P - r)) + 12 * r) ∧
      C = h ^ 2 * (s + t) ^ 2 * ((P - r) - (Q - r)) ∧
      g₂ ^ 3 - 27 * g₃ ^ 2 = (P - Q) * (h ^ 4 * (B * (A ^ 2 * (B * ((P - r) - (Q - r)))
        - 16 * (B * ((P - r) - (Q - r))) ^ 2 + 72 * A * (C * ((P - r) - (Q - r))))
        - C * (4 * A ^ 3 + 432 * (C * ((P - r) - (Q - r)))))) := by sorry
