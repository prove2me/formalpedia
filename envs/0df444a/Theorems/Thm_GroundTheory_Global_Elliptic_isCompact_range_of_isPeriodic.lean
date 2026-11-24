-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_isCompact_range_of_isPeriodic
-- name    : GroundTheory.Global.Elliptic.isCompact_range_of_isPeriodic
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:26.687897+00:00
-- url     : https://prove2.me/theorems/9ad9a3de-9faf-4041-9a34-0a60584f2b10
-- title:
--   Elliptic: is Compact range of is Periodic
-- statement:
--   The Elliptic construction uses the is Compact range of is Periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L78-L80

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
variable (L)

theorem GroundTheory.Global.Elliptic.isCompact_range_of_isPeriodic {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hc : Continuous f) (hf : IsPeriodic L f) : IsCompact (range f) := by sorry
