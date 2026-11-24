-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_injective
-- name    : GroundTheory.Automorphic.coinvariantsTranslate_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:24.274818+00:00
-- url     : https://prove2.me/theorems/da317b40-c6b7-4bf2-a038-11aa29a59f99
-- title:
--   Automorphic: coinvariants Translate injective
-- statement:
--   The Automorphic construction uses the coinvariants Translate injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L116-L123

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (N : Subgroup G)
variable {ρ N}

theorem GroundTheory.Automorphic.coinvariantsTranslate_injective {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (ha' : ∀ n ∈ N, a⁻¹ * n * a ∈ N) :
    Function.Injective (coinvariantsTranslate ρ N a ha) := by sorry
