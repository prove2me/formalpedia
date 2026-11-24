-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_ne_zero_of_isCompact_of_isOpen
-- name    : GroundTheory.Automorphic.Parabolic.relIndex_ne_zero_of_isCompact_of_isOpen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:30.151874+00:00
-- url     : https://prove2.me/theorems/2c00960c-2bab-4ecd-a914-382ac747bcea
-- title:
--   Parabolic: rel Index ne zero of is Compact of is Open
-- statement:
--   The Parabolic construction uses the rel Index ne zero of is Compact of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L344-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L344-L349

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.relIndex_ne_zero_of_isCompact_of_isOpen {K L : Subgroup G} (hK : IsCompact (K : Set G))
    (hL : IsOpen (L : Set G)) : L.relIndex K ≠ 0 := by sorry
