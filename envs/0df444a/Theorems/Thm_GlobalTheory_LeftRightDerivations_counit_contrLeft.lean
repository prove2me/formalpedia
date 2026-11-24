-- Prove2me | Theorems.Thm_GlobalTheory_LeftRightDerivations_counit_contrLeft
-- name    : GlobalTheory.LeftRightDerivations.counit_contrLeft
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:19.429063+00:00
-- url     : https://prove2.me/theorems/60c2b848-3bdb-4244-8c9f-536e487a66d9
-- title:
--   Left Right Derivations: counit contr Left
-- statement:
--   The Left Right Derivations construction uses the counit contr Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L87-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LeftRightDerivations
variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]

theorem GlobalTheory.LeftRightDerivations.counit_contrLeft (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrLeft φ s) =
      φ (contrRight (Coalgebra.counit (R := k)) s) := by sorry
