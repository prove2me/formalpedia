-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_rs_rs
-- name    : GlobalTheory.AffineThickening.rs_rs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:16.205702+00:00
-- url     : https://prove2.me/theorems/f68d1b8b-c1bc-4888-92a6-f9fb0f6d34d7
-- title:
--   Affine Thickening: rs rs
-- statement:
--   The Affine Thickening construction uses the rs rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening

theorem GlobalTheory.AffineThickening.rs_rs {Y : Scheme.{u}} {U V W : Y.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(Y, U)) :
    rs h' (rs h a) = rs (h'.trans h) a := by sorry
