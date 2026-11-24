-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_isAffine_of_mul_eq_zero
-- name    : GlobalTheory.AffineThickening.isAffine_of_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:53.873837+00:00
-- url     : https://prove2.me/theorems/9a05e317-3d0b-4a73-b6ed-bfa775263dd4
-- title:
--   Affine Thickening: is Affine of mul eq zero
-- statement:
--   The Affine Thickening construction uses the is Affine of mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L261-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L261-L306

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}

theorem GlobalTheory.AffineThickening.isAffine_of_mul_eq_zero (i : Z ⟶ Y) [IsClosedImmersion i] [Surjective i] [IsAffine Z]
    (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U),
      (i.app U).hom a = 0 → (i.app U).hom b = 0 → a * b = 0) : IsAffine Y := by sorry
