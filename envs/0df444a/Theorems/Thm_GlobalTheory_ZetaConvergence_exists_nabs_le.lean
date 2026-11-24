-- Prove2me | Theorems.Thm_GlobalTheory_ZetaConvergence_exists_nabs_le
-- name    : GlobalTheory.ZetaConvergence.exists_nabs_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:12:13.689085+00:00
-- url     : https://prove2.me/theorems/0605acdc-223b-4900-91db-cc01aef870d5
-- title:
--   Zeta Convergence: exists nabs le
-- statement:
--   The Zeta Convergence construction uses the exists nabs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegrableZetaIntegrand.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegrableZetaIntegrand.lean#L13-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableZetaIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.ZetaConvergence
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.ZetaConvergence.exists_nabs_le {K : Set k} (hK : IsCompact K) : ∃ B : ℝ, ∀ x : kˣ, (x : k) ∈ K → nabs k x ≤ B := by sorry
