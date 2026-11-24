-- Prove2me | Theorems.Thm_GlobalTheory_TensHead_exists_adjoin_agree
-- name    : GlobalTheory.TensHead.exists_adjoin_agree
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:42.370461+00:00
-- url     : https://prove2.me/theorems/898d9f2e-cffb-40a2-968c-d0932251f042
-- title:
--   Tens Head: exists adjoin agree
-- statement:
--   The Tens Head construction uses the exists adjoin agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleTensorProductOperatorStableCountable.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleTensorProductOperatorStableCountable.lean#L9-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierSchurOfRankLeAleph0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead

theorem GlobalTheory.TensHead.exists_adjoin_agree {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (A : Set (Module.End ℂ V)) (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hA : ∀ U : Submodule ℂ V, Stab A U → U = ⊥ ∨ U = ⊤) (p : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ A, ∀ m ∈ s, p m = r m := by sorry
