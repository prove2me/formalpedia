-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_rootMultiplicity_zero_locked
-- name    : FriedCrossing.Spectral.rootMultiplicity_zero_locked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:15.194325+00:00
-- url     : https://prove2.me/theorems/1eb4f6b4-45f7-5a1e-959a-d712e44f8f47
-- title:
--   Spectral: root Multiplicity zero locked
-- statement:
--   The Spectral construction uses the root Multiplicity zero locked property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L661-L669
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L661-L669

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.rootMultiplicity_zero_locked {scl : ℝ} (hscl : scl ≠ 0) (e₁ e₂ : ℝ) :
    ((X - C scl) * (X - C (0 : ℝ)) * Qpoly e₁ e₂).rootMultiplicity 0 =
      1 + (Qpoly e₁ e₂).rootMultiplicity 0 := by sorry
