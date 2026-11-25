-- Prove2me | Theorems.Thm_GlobalTheory_OrbitDenom_vE_norm_prod
-- name    : GlobalTheory.OrbitDenom.vE_norm_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:12.086819+00:00
-- url     : https://prove2.me/theorems/abbe7e24-79eb-4f11-9ec3-f4ac4bac1490
-- title:
--   Orbit Denom: v E norm prod
-- statement:
--   The Orbit Denom construction uses the v E norm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L338-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L338-L360

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrbitDenom
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.OrbitDenom.vE_norm_prod (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {ι : Type} (x : ι → E)
    (hx : ∀ i, IsUnit (x i)) (s : Finset ι) :
    vE L ϖ ((∏ i ∈ s, x i) * L.cj (∏ i ∈ s, x i)) = ∑ i ∈ s, vE L ϖ (x i * L.cj (x i)) := by sorry
