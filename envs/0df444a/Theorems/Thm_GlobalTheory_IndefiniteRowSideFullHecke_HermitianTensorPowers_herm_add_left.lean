-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HermitianTensorPowers_herm_add_left
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.herm_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:56.046869+00:00
-- url     : https://prove2.me/theorems/35fcac23-d7fb-4adb-a9e4-5a976c3de1b1
-- title:
--   Hermitian Tensor Powers: herm add left
-- statement:
--   The Hermitian Tensor Powers construction uses the herm add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HermitianTensorPowers.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HermitianTensorPowers.lean#L56-L57

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    herm Hm (z + z') w = herm Hm z w + herm Hm z' w := by sorry
