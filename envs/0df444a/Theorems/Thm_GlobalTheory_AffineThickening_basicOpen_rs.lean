-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_basicOpen_rs
-- name    : GlobalTheory.AffineThickening.basicOpen_rs
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:30.644168+00:00
-- url     : https://prove2.me/theorems/a17f1e41-5caa-4a59-8f18-ad507d42ceed
-- title:
--   Affine Thickening: basic Open rs
-- statement:
--   The Affine Thickening construction uses the basic Open rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L18-L20

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

theorem GlobalTheory.AffineThickening.basicOpen_rs {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    Y.basicOpen (rs h a) = V ⊓ Y.basicOpen a := by sorry
