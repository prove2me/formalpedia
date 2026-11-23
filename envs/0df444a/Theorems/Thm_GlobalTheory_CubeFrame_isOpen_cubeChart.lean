-- Prove2me | Theorems.Thm_GlobalTheory_CubeFrame_isOpen_cubeChart
-- name    : GlobalTheory.CubeFrame.isOpen_cubeChart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:31.4598+00:00
-- url     : https://prove2.me/theorems/686fd0ac-85aa-4df1-8ccb-eab604222e88
-- title:
--   Cube Frame: is Open cube Chart
-- statement:
--   The Cube Frame construction uses the is Open cube Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}
omit [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem GlobalTheory.CubeFrame.isOpen_cubeChart {X : Type*} [TopologicalSpace X] {p : X → Fin 3 → E}
    (hp : Continuous p) {V : Finset (Fin 3) → Set E} (hV : ∀ I, IsOpen (V I)) :
    IsOpen {y | ∀ I : Finset (Fin 3), ∑ a ∈ I, p y a ∈ V I} := by sorry
