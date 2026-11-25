-- Prove2me | Theorems.Thm_GlobalTheory_HL_GlobalWit_hermitianIsometry_selfDual_eq_of_thetaClose
-- name    : GlobalTheory.HL.GlobalWit.hermitianIsometry_selfDual_eq_of_thetaClose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:33.932104+00:00
-- url     : https://prove2.me/theorems/8bb096ed-0ac4-5f61-87b9-718c4b5a87c0
-- title:
--   Global Wit: hermitian Isometry self Dual eq of theta Close
-- statement:
--   The Global Wit construction uses the hermitian Isometry self Dual eq of theta Close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalHermitianFramesRationalWitnessesPhase.lean#L73-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalHermitianFramesRationalWitnessesPhase.lean#L73-L109

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationUnipotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalHermitianFramesRationalWitnessesPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlobalWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem GlobalTheory.HL.GlobalWit.hermitianIsometry_selfDual_eq_of_thetaClose (S : Frames L r k) {Λ I : Submodule L.O S.V} (hsd : IsSD L S.Hm Λ) {m w : S.GLV}
    (hm : m ∈ isomG L S.Hm) (hw : w ∈ isomG L S.Hm) (hI : Λ = m • I)
    (h1 : ∀ x ∈ Λ, S.InTh Λ (m (w.symm x) - x)) :
    Λ = w • I ∧ ∀ x ∈ I, S.InTh Λ (m x - w x) := by sorry
