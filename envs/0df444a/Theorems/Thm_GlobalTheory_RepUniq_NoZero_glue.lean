-- Prove2me | Theorems.Thm_GlobalTheory_RepUniq_NoZero_glue
-- name    : GlobalTheory.RepUniq.NoZero.glue
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:54.019906+00:00
-- url     : https://prove2.me/theorems/2396ffc4-1cd5-5e32-af27-332f628783ad
-- title:
--   No Zero: glue
-- statement:
--   The No Zero construction uses the glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L33-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}

theorem GlobalTheory.RepUniq.NoZero.glue {W : T.Opens} {f f' : σ → Γ(T, W)} (hf : NoZero f)
    (H : ∀ t ∈ W, ∃ (V : T.Opens) (h : V ≤ W), t ∈ V ∧ ∃ u : Γ(T, V), IsUnit u ∧
      ∀ i, resG T h (f' i) = u * resG T h (f i)) :
    ∃ u : Γ(T, W), IsUnit u ∧ ∀ i, f' i = u * f i := by sorry
