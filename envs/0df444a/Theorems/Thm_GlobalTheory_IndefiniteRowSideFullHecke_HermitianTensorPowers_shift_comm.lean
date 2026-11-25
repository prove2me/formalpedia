-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HermitianTensorPowers_shift_comm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.shift_comm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:23.725679+00:00
-- url     : https://prove2.me/theorems/6306f87a-682a-4a49-82d6-d05470035587
-- title:
--   Hermitian Tensor Powers: shift comm
-- statement:
--   The Hermitian Tensor Powers construction uses the shift comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HermitianTensorPowers.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HermitianTensorPowers.lean#L71-L81

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.shift_comm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (k : ℕ) (v w : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    shift Hm k v (shift Hm k w θ) z = commVal Hm k v w * shift Hm k w (shift Hm k v θ) z := by sorry
