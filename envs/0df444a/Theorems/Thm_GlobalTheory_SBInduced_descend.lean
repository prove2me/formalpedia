-- Prove2me | Theorems.Thm_GlobalTheory_SBInduced_descend
-- name    : GlobalTheory.SBInduced.descend
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:57.292731+00:00
-- url     : https://prove2.me/theorems/7c301bd5-6733-48a3-806e-b63826c4e97e
-- title:
--   SBInduced: descend
-- statement:
--   The SBInduced construction uses the descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatSweepSmoothlyInduced.lean#L52-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatSweepSmoothlyInduced.lean#L52-L90

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

theorem GlobalTheory.SBInduced.descend [T2Space X] (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) (H : G → SB Y)
    (hU : ∀ᶠ u in 𝓝 (1 : G), ∀ g, H (g * u) = H g)
    (hfib : ∀ y g y' g', r (j y) g = r (j y') g' → (H g).1 y = (H g').1 y') :
    ∃ Φ : SB X, ∀ g y, Φ.1 (r (j y) g) = (H g).1 y := by sorry
