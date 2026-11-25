-- Prove2me | Theorems.Thm_GlobalTheory_HL_Defect_exponents_and_defect
-- name    : GlobalTheory.HL.Defect.exponents_and_defect
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:23:19.722749+00:00
-- url     : https://prove2.me/theorems/14f1fa3b-2c63-43c1-b3e2-40bcc42f0e77
-- title:
--   Defect: exponents and defect
-- statement:
--   The Defect construction uses the exponents and defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermExponentsNonnegAndDefectGroupBound.lean#L355-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermExponentsNonnegAndDefectGroupBound.lean#L355-L459

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.Defect.exponents_and_defect : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 ≤ S.a ∧ 0 ≤ S.vD ∧ (∀ l, S.D l ∈ L.O) ∧ (S.q : ℝ) ^ S.a ≤ S.Hp ∧ 1 ≤ S.Hp ∧ (∃ i : ℕ, (i : ℤ) ≤ S.a ∧ S.be d Λ = S.q ^ i) ∧ (S.BBzero d Λ ↔ S.be d Λ = 1) ∧ (¬ S.BBzero d Λ → (S.q : ℝ) ≤ S.Hp) ∧ (∀ y ∈ S.sat Λ, algebraMap F E ((S.ϖ : F) ^ S.a) • y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ := by sorry
