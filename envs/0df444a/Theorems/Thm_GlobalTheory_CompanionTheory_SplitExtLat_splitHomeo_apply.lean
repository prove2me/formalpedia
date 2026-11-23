-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_splitHomeo_apply
-- name    : GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:35.527805+00:00
-- url     : https://prove2.me/theorems/f10fc88a-7a99-40bf-99ef-33f6b4280587
-- title:
--   Split Ext Lat: split Homeo apply
-- statement:
--   The Split Ext Lat construction uses the split Homeo apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitHomeoApply.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitHomeoApply.lean#L36-L39

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat
variable {P G₁ : Type} [Group P] [Group G₁]

theorem GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) (z : π.ker × G₁) :
    splitHomeo ι π hι hπ h z = (z.1 : P) * ι z.2 := by sorry

attribute [defeq] GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply
