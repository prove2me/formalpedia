-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_prod_le_prod_range_of_rank
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.prod_le_prod_range_of_rank
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:38.624478+00:00
-- url     : https://prove2.me/theorems/23a0e766-0967-524e-8602-d24e947f1ff1
-- title:
--   Wave Grid Lift Grid: prod le prod range of rank
-- statement:
--   The Wave Grid Lift Grid construction uses the prod le prod range of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L34-L49

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.prod_le_prod_range_of_rank (A : Finset ℕ) (F : ℕ → ℝ) (φ : ℕ → ℕ) (w : ℕ → ℝ) (k : ℕ)
    (hF0 : ∀ s ∈ A, 0 ≤ F s) (hF : ∀ s ∈ A, F s ≤ w (φ s)) (hinj : Set.InjOn φ A)
    (hmap : ∀ s ∈ A, φ s < k) (hw : ∀ j, 1 ≤ w j) :
    ∏ s ∈ A, F s ≤ ∏ j ∈ range k, w j := by sorry
