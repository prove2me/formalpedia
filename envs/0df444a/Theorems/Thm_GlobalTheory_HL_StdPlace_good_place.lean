-- Prove2me | Theorems.Thm_GlobalTheory_HL_StdPlace_good_place
-- name    : GlobalTheory.HL.StdPlace.good_place
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:23:01.766593+00:00
-- url     : https://prove2.me/theorems/a5e7fc04-257e-4963-9eda-df22fbe2feec
-- title:
--   Std Place: good place
-- statement:
--   The Std Place construction uses the good place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CoordinateLatticeUniqueTermAlmostAllPlaces.lean#L127-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CoordinateLatticeUniqueTermAlmostAllPlaces.lean#L127-L195

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEquivOfRetractions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_Equality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralOfMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HmUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalHermitianFramesGoodAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsOrthonormalSameIntegralSpanUnimodularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianTermSplitsUnimodularComplementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeUnimodularGeneratorsExponentZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCoordinateLatticeIsTermTrivialWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerFramesCoordinateLatticeGoodPlaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GoodPlaceGramInvariantMinorsValuationZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoordinateLatticeUniqueTermAlmostAllPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StdPlace

theorem GlobalTheory.HL.StdPlace.good_place {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k) (hG : Good S) :
    S.Hp = 1 ∧ S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 ∧ ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 ∧
      S.om d₀ (coordLat S) = 1 ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d₀ = S.complementReferenceCompactSubgroup ∧
      (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • coordLat S) ∧
      (∀ Λ, S.IsTerm d₀ Λ → S.Fr d₀ Λ = S.frameCls S.f S.f' → Λ = coordLat S) ∧
      ∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀ := by sorry
