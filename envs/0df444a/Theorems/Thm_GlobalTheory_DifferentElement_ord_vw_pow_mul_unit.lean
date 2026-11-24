-- Prove2me | Theorems.Thm_GlobalTheory_DifferentElement_ord_vw_pow_mul_unit
-- name    : GlobalTheory.DifferentElement.ord_vw_pow_mul_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:00.897789+00:00
-- url     : https://prove2.me/theorems/0241c094-b293-4adc-b055-d7e39bff2a40
-- title:
--   Different Element: ord vw pow mul unit
-- statement:
--   The Different Element construction uses the ord vw pow mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominator.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominator.lean#L28-L39

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

theorem GlobalTheory.DifferentElement.ord_vw_pow_mul_unit (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Field K]
    [Algebra O K] [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    ord_vw O (algebraMap O K (ϖ ^ n * u)) = n := by sorry
