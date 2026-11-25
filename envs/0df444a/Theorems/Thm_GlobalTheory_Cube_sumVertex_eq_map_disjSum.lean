-- Prove2me | Theorems.Thm_GlobalTheory_Cube_sumVertex_eq_map_disjSum
-- name    : GlobalTheory.Cube.sumVertex_eq_map_disjSum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:06:11.097138+00:00
-- url     : https://prove2.me/theorems/9d1e6718-3578-5cf4-95bb-3252403c0fe6
-- title:
--   Cube: sum Vertex eq map disj Sum
-- statement:
--   The Cube construction uses the sum Vertex eq map disj Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L730-L734
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L730-L734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]

theorem GlobalTheory.Cube.sumVertex_eq_map_disjSum (s : Finset ι) (t : Finset κ) :
    sumVertex s t = (s.disjSum t).map toLex.toEmbedding := by sorry
