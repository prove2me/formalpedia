-- Prove2me | Theorems.Thm_GlobalTheory_AnDim_hasHoloImm_of_regularLocus
-- name    : GlobalTheory.AnDim.hasHoloImm_of_regularLocus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:13.809053+00:00
-- url     : https://prove2.me/theorems/62c97bda-7348-4082-91d9-7cb2bf5fbaf0
-- title:
--   An Dim: has Holo Imm of regular Locus
-- statement:
--   The An Dim construction uses the has Holo Imm of regular Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L98-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L98-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.AnDim.hasHoloImm_of_regularLocus {A : FinHolAtlas d X} {T : Set X} {n k : ℕ} (hk : k ≤ n)
    (h : (regularLocus A T n).Nonempty) : HasHoloImm A T k := by sorry
