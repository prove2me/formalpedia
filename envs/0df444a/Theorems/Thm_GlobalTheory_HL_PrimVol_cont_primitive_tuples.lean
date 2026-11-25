-- Prove2me | Theorems.Thm_GlobalTheory_HL_PrimVol_cont_primitive_tuples
-- name    : GlobalTheory.HL.PrimVol.cont_primitive_tuples
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:55.899472+00:00
-- url     : https://prove2.me/theorems/8bcc857e-2768-48a6-a59e-e22a7b676e4c
-- title:
--   Prim Vol: cont primitive tuples
-- statement:
--   The Prim Vol construction uses the cont primitive tuples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesHermitianGramCosetContent.lean#L392-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesHermitianGramCosetContent.lean#L392-L465

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

theorem GlobalTheory.HL.PrimVol.cont_primitive_tuples : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m : ℕ, 2 * m + 3 ≤ n → ∀ B : Set (Matrix (Fin m) (Fin m) E), (∀ X ∈ B, X ∈ hermLat L m) → IsCO (hermLat L m) B → IsCO (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (hermLat L m) B ≤ 2 * cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ≤ 2 * cont (hermLat L m) B := by sorry
