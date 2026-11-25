-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply
-- name    : GroundTheory.Automorphic.HeckeAlgebra.mul_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:42.730803+00:00
-- url     : https://prove2.me/theorems/cded46a2-c1f0-481a-80e1-e7b7b087387f
-- title:
--   Hecke Algebra: mul apply
-- statement:
--   The Hecke Algebra construction uses the mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebra.lean#L385-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebra.lean#L385-L385

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
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
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
open GroundTheory.Automorphic.HeckeAlgebra
variable {μ : Measure G}

theorem GroundTheory.Automorphic.HeckeAlgebra.mul_apply (f g : HeckeAlgebra μ) (x : G) : (f * g) x = ∫ y, f y * g (y⁻¹ * x) ∂μ := by sorry
