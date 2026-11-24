-- Prove2me | Theorems.Thm_GlobalTheory_schwartzBruhat_eventually_invariant_of_continuous_action
-- name    : GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:20:40.053798+00:00
-- url     : https://prove2.me/theorems/46c0febb-abba-4609-ac2b-70150ff842de
-- title:
--   Global Theory: schwartz Bruhat eventually invariant of continuous action
-- statement:
--   The Global Theory construction uses the schwartz Bruhat eventually invariant of continuous action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatEventuallyInvariantOfContinuousAct.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatEventuallyInvariantOfContinuousAct.lean#L7-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatEventuallyInvariantOfContinuousAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
open GlobalTheory

theorem GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
      (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) →
      Continuous (fun p : X × G => r p.1 p.2) →
      ∀ Φ : SB X, ∀ᶠ u in nhds (1 : G), ∀ x, Φ.1 (r x u) = Φ.1 x := by sorry
