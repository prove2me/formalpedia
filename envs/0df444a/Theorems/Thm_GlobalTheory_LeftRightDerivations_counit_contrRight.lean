-- Prove2me | Theorems.Thm_GlobalTheory_LeftRightDerivations_counit_contrRight
-- name    : GlobalTheory.LeftRightDerivations.counit_contrRight
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:15.21626+00:00
-- url     : https://prove2.me/theorems/f59248ea-2446-4750-88ed-57e1c7013d7a
-- title:
--   Left Right Derivations: counit contr Right
-- statement:
--   The Left Right Derivations construction uses the counit contr Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L79-L85

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

theorem GlobalTheory.LeftRightDerivations.counit_contrRight (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrRight φ s) =
      φ (contrLeft (Coalgebra.counit (R := k)) s) := by sorry
