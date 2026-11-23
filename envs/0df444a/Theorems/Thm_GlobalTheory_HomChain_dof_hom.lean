-- Prove2me | Theorems.Thm_GlobalTheory_HomChain_dof_hom
-- name    : GlobalTheory.HomChain.dof_hom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:01.828675+00:00
-- url     : https://prove2.me/theorems/6ef6d07c-04fa-465b-9a5f-ec3dc13d7f92
-- title:
--   Hom Chain: dof hom
-- statement:
--   The Hom Chain construction uses the dof hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LawRightUnit.lean#L27-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LawRightUnit.lean#L27-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartTrans
open GlobalTheory GlobalTheory.HomChain
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.HomChain.dof_hom (G G' : FGLaw k d) (α : Pt k 1 d) (hα : ∀ i, constantCoeff (α i) = 0)
    (hom : comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof G.F u (ev (n := 1) ![α] g) = ev (n := 1) ![α] (Dof G'.F ((dLin α).mulVec u) g) := by sorry
