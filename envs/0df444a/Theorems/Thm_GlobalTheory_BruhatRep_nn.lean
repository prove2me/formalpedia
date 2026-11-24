-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_nn
-- name    : GlobalTheory.BruhatRep.nn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:03:40.914239+00:00
-- url     : https://prove2.me/theorems/d47e854e-da83-4ebc-9a4b-c79ff10fdbee
-- title:
--   Bruhat Rep: nn
-- statement:
--   The Bruhat Rep construction uses the nn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L57-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)

theorem GlobalTheory.BruhatRep.nn (hn : ∀ a b, n (a + b) = n a * n b) (a b : K) (X : M) : X * n a * n b = X * n (a + b) := by sorry
