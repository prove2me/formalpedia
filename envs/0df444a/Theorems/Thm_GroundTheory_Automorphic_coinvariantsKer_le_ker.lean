-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coinvariantsKer_le_ker
-- name    : GroundTheory.Automorphic.coinvariantsKer_le_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:56.665251+00:00
-- url     : https://prove2.me/theorems/91b25c26-7871-4058-b3d5-26ad81842591
-- title:
--   Automorphic: coinvariants Ker le ker
-- statement:
--   The Automorphic construction uses the coinvariants Ker le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L19-L23

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
variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ N V)
omit [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N]
  [TotallyDisconnectedSpace N]

theorem GroundTheory.Automorphic.coinvariantsKer_le_ker (K : Subgroup N) :
    coinvariantsKer ρ K ≤ Representation.Coinvariants.ker ρ := by sorry
