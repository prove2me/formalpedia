-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_mem_range_appLE_chart_iff
-- name    : GlobalTheory.ZJ.mem_range_appLE_chart_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:05.884332+00:00
-- url     : https://prove2.me/theorems/84a95f56-62fa-5d88-8e7d-c00d1b916402
-- title:
--   ZJ: mem range app LE chart iff
-- statement:
--   The ZJ construction uses the mem range app LE chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemRangeAppLEChartIff.lean#L41-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemRangeAppLEChartIff.lean#L41-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

theorem GlobalTheory.ZJ.mem_range_appLE_chart_iff {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)
    (W : Y.Opens) (a : Fin (N + 1)) (h : W ≤ φ ⁻¹ᵁ chart R N a) (u : Γ(Y, W)) :
    u ∈ Set.range (φ.appLE (chart R N a) W h).hom ↔
      u ∈ Subring.closure (Set.range ((φ ≫ PSpace.str R N).appLE ⊤ W le_top).hom ∪
        Set.range (pullRatio φ W a h)) := by sorry
