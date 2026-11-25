-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_differentiableOn_modularJC
-- name    : GroundTheory.Global.Elliptic.differentiableOn_modularJC
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:05:13.153812+00:00
-- url     : https://prove2.me/theorems/4bdbdcaa-68db-596d-9512-32f227027f13
-- title:
--   Elliptic: differentiable On modular JC
-- statement:
--   The Elliptic construction uses the differentiable On modular JC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariantSurjective.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariantSurjective.lean#L53-L60

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

theorem GroundTheory.Global.Elliptic.differentiableOn_modularJC : DifferentiableOn ℂ modularJC {z : ℂ | 0 < z.im} := by sorry
