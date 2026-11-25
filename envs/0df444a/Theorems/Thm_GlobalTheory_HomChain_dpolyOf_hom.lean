-- Prove2me | Theorems.Thm_GlobalTheory_HomChain_dpolyOf_hom
-- name    : GlobalTheory.HomChain.dpolyOf_hom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:43.503285+00:00
-- url     : https://prove2.me/theorems/d3c744de-b1e5-48be-8ee8-d800c7dc8e35
-- title:
--   Hom Chain: dpoly Of hom
-- statement:
--   The Hom Chain construction uses the dpoly Of hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LawRightUnit.lean#L61-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LawRightUnit.lean#L61-L90

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

theorem GlobalTheory.HomChain.dpolyOf_hom :
    ∀ (k : Type) [CommRing k] (d : ℕ) (G G' : FGLaw k d) (α : Pt k 1 d),
      (∀ i, constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k) (g : PS k 1 d),
        DpolyOf G.F u Q (ev (n := 1) ![α] g) =
          ev (n := 1) ![α] (DpolyOf G'.F (fun l => (dLin α).mulVec (u l)) Q g) := by sorry
