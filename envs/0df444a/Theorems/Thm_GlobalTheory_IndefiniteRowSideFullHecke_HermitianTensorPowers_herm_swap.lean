-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HermitianTensorPowers_herm_swap
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.herm_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:53.843429+00:00
-- url     : https://prove2.me/theorems/f7e87bfa-c7f7-4063-87e6-91cec5b5d94a
-- title:
--   Hermitian Tensor Powers: herm swap
-- statement:
--   The Hermitian Tensor Powers construction uses the herm swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HermitianTensorPowers.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HermitianTensorPowers.lean#L59-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v w : Fin g → ℂ) :
    herm Hm w v = starRingEnd ℂ (herm Hm v w) := by sorry
