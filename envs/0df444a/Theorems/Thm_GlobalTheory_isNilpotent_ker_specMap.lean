-- Prove2me | Theorems.Thm_GlobalTheory_isNilpotent_ker_specMap
-- name    : GlobalTheory.isNilpotent_ker_specMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:01.526352+00:00
-- url     : https://prove2.me/theorems/156f525e-387d-4dbd-8ade-db452b0df0af
-- title:
--   Global Theory: is Nilpotent ker spec Map
-- statement:
--   The Global Theory construction uses the is Nilpotent ker spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L226-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L226-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory

theorem GlobalTheory.isNilpotent_ker_specMap {R R₀ : CommRingCat.{u}} (π : R ⟶ R₀)
    (hπ : IsNilpotent (RingHom.ker π.hom)) : IsNilpotent (Spec.map π).ker := by sorry
