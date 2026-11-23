-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_map_mem_of_monomial
-- name    : GroundTheory.Automorphic.HarishChandra.map_mem_of_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:22.21823+00:00
-- url     : https://prove2.me/theorems/6a07794c-5a19-48b4-bd03-c846ec53b23d
-- title:
--   Harish Chandra: map mem of monomial
-- statement:
--   The Harish Chandra construction uses the map mem of monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L195-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L195-L199

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.map_mem_of_monomial (L : Poly n →ₗ[ℂ] Poly n) (P : Submodule ℂ (Poly n))
    (Q : (Fin n × Fin n →₀ ℕ) → Prop) {f : Poly n} (hf : ∀ s, coeff s f ≠ 0 → Q s)
    (h : ∀ s (c : ℂ), Q s → L (monomial s c) ∈ P) : L f ∈ P := by sorry
