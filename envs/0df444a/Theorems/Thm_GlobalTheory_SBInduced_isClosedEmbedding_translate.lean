-- Prove2me | Theorems.Thm_GlobalTheory_SBInduced_isClosedEmbedding_translate
-- name    : GlobalTheory.SBInduced.isClosedEmbedding_translate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:24.942954+00:00
-- url     : https://prove2.me/theorems/806ec325-25fb-416a-accb-1d2cee99e3e1
-- title:
--   SBInduced: is Closed Embedding translate
-- statement:
--   The SBInduced construction uses the is Closed Embedding translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatSweepSmoothlyInduced.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatSweepSmoothlyInduced.lean#L16-L27

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
omit [IsTopologicalGroup G]

theorem GlobalTheory.SBInduced.isClosedEmbedding_translate (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) (g : G) : IsClosedEmbedding fun y => r (j y) g := by sorry
