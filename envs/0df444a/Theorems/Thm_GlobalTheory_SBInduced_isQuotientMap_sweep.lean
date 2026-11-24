-- Prove2me | Theorems.Thm_GlobalTheory_SBInduced_isQuotientMap_sweep
-- name    : GlobalTheory.SBInduced.isQuotientMap_sweep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:30.114369+00:00
-- url     : https://prove2.me/theorems/3f4f77f5-4821-4fa6-a48c-b03eaa65c69a
-- title:
--   SBInduced: is Quotient Map sweep
-- statement:
--   The SBInduced construction uses the is Quotient Map sweep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatSweepSmoothlyInduced.lean#L29-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatSweepSmoothlyInduced.lean#L29-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatEventuallyInvariantOfContinuousAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter
open GlobalTheory GlobalTheory.SBInduced
variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]

theorem GlobalTheory.SBInduced.isQuotientMap_sweep (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) :
    IsQuotientMap fun p : Y × K => r (j p.1) p.2 := by sorry
