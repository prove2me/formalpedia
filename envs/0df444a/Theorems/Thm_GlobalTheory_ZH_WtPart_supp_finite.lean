-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtPart_supp_finite
-- name    : GlobalTheory.ZH.WtPart.supp_finite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:02:30.528253+00:00
-- url     : https://prove2.me/theorems/6da19457-ce12-42ef-96e3-a98b3a8f572d
-- title:
--   Wt Part: supp finite
-- statement:
--   The Wt Part construction uses the supp finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsPartPartSec.lean#L181-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsPartPartSec.lean#L181-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
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
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}

theorem GlobalTheory.ZH.WtPart.supp_finite (φ : (Φ.H d).Sec) : (Φ.supp φ).Finite := by sorry
