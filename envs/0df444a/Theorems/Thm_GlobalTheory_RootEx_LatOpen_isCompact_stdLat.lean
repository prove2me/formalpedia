-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_LatOpen_isCompact_stdLat
-- name    : GlobalTheory.RootEx.LatOpen.isCompact_stdLat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:24.272712+00:00
-- url     : https://prove2.me/theorems/f17043ad-1b4c-431b-84eb-bf062b7349aa
-- title:
--   Lat Open: is Compact std Lat
-- statement:
--   The Lat Open construction uses the is Compact std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenAndRelIndexNeZero.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenAndRelIndexNeZero.lean#L50-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenAndRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.LatOpen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

theorem GlobalTheory.RootEx.LatOpen.isCompact_stdLat : IsCompact (stdLat k ι : Set (ι → k)) := by sorry
