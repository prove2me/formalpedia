-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantDbarLeibniz_homCovDel_leibniz
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.homCovDel_leibniz
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:06.455427+00:00
-- url     : https://prove2.me/theorems/eb96c070-4a15-5e54-993e-282c46690d04
-- title:
--   Covariant Dbar Leibniz: hom Cov Del leibniz
-- statement:
--   The Covariant Dbar Leibniz construction uses the hom Cov Del leibniz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L144-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean#L144-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l k : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.homCovDel_leibniz (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) {T : E → Matrix l m ℂ}
    {S : E → Matrix m k ℂ} {z : E} (hT : MContDiffAt 1 T z) (hS : MContDiffAt 1 S z) (ξ : E) :
    mdel (fun x => T x * S x) z ξ + conn B z ξ * (T z * S z) =
      homCovDel A B T z ξ * S z + T z * (mdel S z ξ + conn A z ξ * S z) := by sorry
