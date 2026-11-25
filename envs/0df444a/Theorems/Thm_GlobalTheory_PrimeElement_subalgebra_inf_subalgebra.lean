-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_subalgebra_inf_subalgebra
-- name    : GlobalTheory.PrimeElement.subalgebra_inf_subalgebra
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:20.886619+00:00
-- url     : https://prove2.me/theorems/da303c27-acd0-5b8a-b284-c52b5aeabb10
-- title:
--   Prime Element: subalgebra inf subalgebra
-- statement:
--   The Prime Element construction uses the subalgebra inf subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L384-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L384-L396

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeElement

theorem GlobalTheory.PrimeElement.subalgebra_inf_subalgebra {R : Type*} [CommRing R] [IsDomain R] {π : R}
    [(Ideal.span {π}).IsPrime] (hπ : π ≠ 0) (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Localization.subalgebra.ofField K (Submonoid.powers π)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hπ) ⊓
      Localization.subalgebra.ofField K (Ideal.span {π}).primeCompl
        (Ideal.span {π}).primeCompl_le_nonZeroDivisors = ⊥ := by sorry
