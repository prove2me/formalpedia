-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_LatOpen_eventually_smul_mem
-- name    : GlobalTheory.RootEx.LatOpen.eventually_smul_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:48.730007+00:00
-- url     : https://prove2.me/theorems/4856518d-f1cc-40e4-928d-2c7a0dd579bc
-- title:
--   Lat Open: eventually smul mem
-- statement:
--   The Lat Open construction uses the eventually smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenAndRelIndexNeZero.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenAndRelIndexNeZero.lean#L13-L32

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

theorem GlobalTheory.RootEx.LatOpen.eventually_smul_mem (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) (x : ι → k) :
    ∀ᶠ t in nhds (0 : k), t • x ∈ L := by sorry
