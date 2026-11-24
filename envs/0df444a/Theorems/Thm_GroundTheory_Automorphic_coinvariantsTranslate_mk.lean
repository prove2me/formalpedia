-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
-- name    : GroundTheory.Automorphic.coinvariantsTranslate_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:02.582719+00:00
-- url     : https://prove2.me/theorems/c850f8d0-da78-4fb2-b335-d502420f89cb
-- title:
--   Automorphic: coinvariants Translate mk
-- statement:
--   The Automorphic construction uses the coinvariants Translate mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L102-L104

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

theorem GroundTheory.Automorphic.coinvariantsTranslate_mk {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (u : V) :
    coinvariantsTranslate ρ N a ha (Representation.Coinvariants.mk _ u) =
      Representation.Coinvariants.mk _ (ρ a u) := by sorry

attribute [defeq] GroundTheory.Automorphic.coinvariantsTranslate_mk
