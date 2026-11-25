-- Prove2me | Theorems.Thm_GlobalTheory_normalisation_finite_local_complete_of_mixedChar
-- name    : GlobalTheory.normalisation_finite_local_complete_of_mixedChar
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:13.65827+00:00
-- url     : https://prove2.me/theorems/be1ad9ea-b5d4-451f-aa9a-a54d6c8655a3
-- title:
--   Global Theory: normalisation finite local complete of mixed Char
-- statement:
--   The Global Theory construction uses the normalisation finite local complete of mixed Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralClosureFiniteLocalCompleteMixedChar.lean#L173-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralClosureFiniteLocalCompleteMixedChar.lean#L173-L195

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.normalisation_finite_local_complete_of_mixedChar :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      Module.Finite S (integralClosure S (FractionRing S)) ∧
        ∃ _ : IsLocalRing (integralClosure S (FractionRing S)),
          IsNoetherianRing (integralClosure S (FractionRing S)) ∧
          IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S)))
            (integralClosure S (FractionRing S)) := by sorry
