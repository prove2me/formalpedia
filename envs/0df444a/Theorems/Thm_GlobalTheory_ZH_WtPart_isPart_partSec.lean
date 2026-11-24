-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtPart_isPart_partSec
-- name    : GlobalTheory.ZH.WtPart.isPart_partSec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:12.239923+00:00
-- url     : https://prove2.me/theorems/5fe30fe8-080d-4e72-a030-616ecb6397ce
-- title:
--   Wt Part: is Part part Sec
-- statement:
--   The Wt Part construction uses the is Part part Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsPartPartSec.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsPartPartSec.lean#L175-L179

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

theorem GlobalTheory.ZH.WtPart.isPart_partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : Φ.IsPart α φ (partSec Φ φ α) := by sorry
