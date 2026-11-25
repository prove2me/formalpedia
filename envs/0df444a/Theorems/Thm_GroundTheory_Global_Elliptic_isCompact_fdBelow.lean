-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_isCompact_fdBelow
-- name    : GroundTheory.Global.Elliptic.isCompact_fdBelow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:54:43.883395+00:00
-- url     : https://prove2.me/theorems/97dac97b-c897-442c-989c-31fe6438427e
-- title:
--   Elliptic: is Compact fd Below
-- statement:
--   The Elliptic construction uses the is Compact fd Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariantSurjective.lean#L99-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariantSurjective.lean#L99-L110

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic

theorem GroundTheory.Global.Elliptic.isCompact_fdBelow (A : ℝ) : IsCompact (fdBelow A) := by sorry
