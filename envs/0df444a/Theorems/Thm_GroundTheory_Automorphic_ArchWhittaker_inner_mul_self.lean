-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_inner_mul_self
-- name    : GroundTheory.Automorphic.ArchWhittaker.inner_mul_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:00.709817+00:00
-- url     : https://prove2.me/theorems/a5d1c763-0cfc-4bea-a51d-969e13bf7ac5
-- title:
--   Arch Whittaker: inner mul self
-- statement:
--   The Arch Whittaker construction uses the inner mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set

theorem GroundTheory.Automorphic.ArchWhittaker.inner_mul_self (z q : ℂ) : inner ℝ z (q * z) = q.re * ‖z‖ ^ 2 := by sorry
