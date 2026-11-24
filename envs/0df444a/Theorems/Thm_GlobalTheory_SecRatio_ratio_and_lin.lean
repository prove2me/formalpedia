-- Prove2me | Theorems.Thm_GlobalTheory_SecRatio_ratio_and_lin
-- name    : GlobalTheory.SecRatio.ratio_and_lin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:50:53.317991+00:00
-- url     : https://prove2.me/theorems/89ba1c3b-72fe-4d89-89fd-07a0a43b25e4
-- title:
--   Sec Ratio: ratio and lin
-- statement:
--   The Sec Ratio construction uses the ratio and lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueIsRatio.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueIsRatio.lean#L95-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
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
open GlobalTheory GlobalTheory.SecRatio
variable {X : Scheme.{0}} {H : LB X}

theorem GlobalTheory.SecRatio.ratio_and_lin : (∀ (X : Scheme.{0}) (H : LB X), H.IsLB → (∀ (s t : H.Sec) (W : X.Opens), W ≤ Out.nonzeroLocus t → ∃! r : Γ(X, W), IsRatio s t W r) ∧ ∀ (k : Type) [CommRing k] (p : X ⟶ Sp k) (J : Type) [Fintype J] (s : J → H.Sec) (a : J → k), ∃! φ : H.Sec, IsLin p s a φ) := by sorry
