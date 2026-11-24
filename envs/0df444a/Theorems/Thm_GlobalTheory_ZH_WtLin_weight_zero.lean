-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtLin_weight_zero
-- name    : GlobalTheory.ZH.WtLin.weight_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:02:36.139604+00:00
-- url     : https://prove2.me/theorems/6b22fa63-9631-40fb-8d9e-14874daa3e53
-- title:
--   Wt Lin: weight zero
-- statement:
--   The Wt Lin construction uses the weight zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffSymmSum.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffSymmSum.lean#L43-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
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
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtLin

theorem GlobalTheory.ZH.WtLin.weight_zero {k : Type} [Field k] (Φ : FibPre k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α 0 = 0 := by sorry
