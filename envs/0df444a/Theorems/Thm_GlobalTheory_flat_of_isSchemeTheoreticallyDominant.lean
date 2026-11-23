-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_isSchemeTheoreticallyDominant
-- name    : GlobalTheory.flat_of_isSchemeTheoreticallyDominant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:07.644481+00:00
-- url     : https://prove2.me/theorems/0d219971-e115-4837-b8c8-c29ea70e4db0
-- title:
--   Global Theory: flat of is Scheme Theoretically Dominant
-- statement:
--   The Global Theory construction uses the flat of is Scheme Theoretically Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L540-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L540-L575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.flat_of_isSchemeTheoreticallyDominant {R : Type u} [CommRing R] [IsDomain R]
    (hR : ∀ (A : Type u) [CommRing A] [Algebra R A], Submodule.torsion R A = ⊥ → Module.Flat R A)
    {X N : Scheme.{u}} (j : X ⟶ N) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (p : N ⟶ Spec (.of R)) [Flat (j ≫ p)] : Flat p := by sorry
