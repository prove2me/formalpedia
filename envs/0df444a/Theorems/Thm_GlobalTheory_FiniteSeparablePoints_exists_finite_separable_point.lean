-- Prove2me | Theorems.Thm_GlobalTheory_FiniteSeparablePoints_exists_finite_separable_point
-- name    : GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:31.638539+00:00
-- url     : https://prove2.me/theorems/45e343a2-3165-4652-8360-b5d9301fc38f
-- title:
--   Finite Separable Points: exists finite separable point
-- statement:
--   The Finite Separable Points construction uses the exists finite separable point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFiniteSeparablePoint.lean#L32-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFiniteSeparablePoint.lean#L32-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteSeparablePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FiniteSeparablePoints

theorem GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p]
    [LocallyOfFiniteType p] (a : Spec (CommRingCat.of Ω) ⟶ X)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by sorry
