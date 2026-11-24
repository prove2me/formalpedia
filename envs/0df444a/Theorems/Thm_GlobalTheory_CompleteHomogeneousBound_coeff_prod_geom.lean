-- Prove2me | Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_coeff_prod_geom
-- name    : GlobalTheory.CompleteHomogeneousBound.coeff_prod_geom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:39.926696+00:00
-- url     : https://prove2.me/theorems/3d0700e9-13e9-474a-90b4-255b890a057b
-- title:
--   Complete Homogeneous Bound: coeff prod geom
-- statement:
--   The Complete Homogeneous Bound construction uses the coeff prod geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L50-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
open GlobalTheory GlobalTheory.CompleteHomogeneousBound

theorem GlobalTheory.CompleteHomogeneousBound.coeff_prod_geom {n : ℕ} (β : Fin n → ℂ) (m : ℕ) :
    coeff m (∏ i, (mk fun k => β i ^ k : ℂ⟦X⟧)) =
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i := by sorry
