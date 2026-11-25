-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtGen_pure_res
-- name    : GlobalTheory.ZH.WtGen.pure_res
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:06.066777+00:00
-- url     : https://prove2.me/theorems/6832756e-c1f0-4698-b40c-457080ceced7
-- title:
--   Wt Gen: pure res
-- statement:
--   The Wt Gen construction uses the pure res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PureSectionRatiosGenerateFunctions.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PureSectionRatiosGenerateFunctions.lean#L61-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k)

theorem GlobalTheory.ZH.WtGen.pure_res {α : Φ.E.X} {φ : (Φ.H 1).Sec} (hφ : Φ.Pure α φ) (l : Φ.N₀.ι) {W : Φ.E.B.left.Opens}
    (h : W ≤ Φ.N₀.U l) : ∃ c : Γ(Φ.E.B.left, W), resG _ (Φ.D.q.left.preimage_mono h) (φ.f l) =
      (Φ.D.q.left.app W).hom c * mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) := by sorry
