-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_LatOpen_isOpen_of_span_eq_top
-- name    : GlobalTheory.RootEx.LatOpen.isOpen_of_span_eq_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:01.413494+00:00
-- url     : https://prove2.me/theorems/7fa1aad7-c405-5e52-b982-6a825655d868
-- title:
--   Lat Open: is Open of span eq top
-- statement:
--   The Lat Open construction uses the is Open of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenAndRelIndexNeZero.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenAndRelIndexNeZero.lean#L34-L48

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

theorem GlobalTheory.RootEx.LatOpen.isOpen_of_span_eq_top [Fintype ι] [DecidableEq ι] (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) : IsOpen (L : Set (ι → k)) := by sorry
