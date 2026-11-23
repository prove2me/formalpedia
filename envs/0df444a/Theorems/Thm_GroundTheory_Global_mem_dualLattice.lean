-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_dualLattice
-- name    : GroundTheory.Global.mem_dualLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:41.96105+00:00
-- url     : https://prove2.me/theorems/e9b697d8-681d-4c35-ad2f-1c3e5ba71421
-- title:
--   Global: mem dual Lattice
-- statement:
--   The Global construction uses the mem dual Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L20-L24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem GroundTheory.Global.mem_dualLattice {L : Submodule ℤ E} {μ : E} :
    μ ∈ dualLattice L ↔ ∀ ℓ ∈ L, ∃ k : ℤ, ⟪μ, ℓ⟫ = k := by sorry
