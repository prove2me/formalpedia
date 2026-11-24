-- Prove2me | Theorems.Thm_GlobalTheory_DifferentElement_exists_intLift
-- name    : GlobalTheory.DifferentElement.exists_intLift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:57.256797+00:00
-- url     : https://prove2.me/theorems/be09edbe-4936-470a-adba-69bb441510cc
-- title:
--   Different Element: exists int Lift
-- statement:
--   The Different Element construction uses the exists int Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominator.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominator.lean#L11-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.DifferentElement

theorem GlobalTheory.DifferentElement.exists_intLift (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (k : Type) [Field k] [Algebra V k] [IsFractionRing V k] (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by sorry
