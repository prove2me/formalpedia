-- Prove2me | Theorems.Thm_GlobalTheory_MoveFine_Mv_add
-- name    : GlobalTheory.MoveFine.Mv_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:42:12.042152+00:00
-- url     : https://prove2.me/theorems/204dad95-7d49-43bc-a705-64f7f316fed5
-- title:
--   Move Fine: Mv add
-- statement:
--   The Move Fine construction uses the Mv add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsFineSubgroupMovesAtLattice.lean#L402-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsFineSubgroupMovesAtLattice.lean#L402-L436

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem GlobalTheory.MoveFine.Mv_add {J : ℕ} (hJ : J ≤ r + 1) {d : S.Datum} {Λ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (A : ℕ)
    (hA : algebraMap F E ((S.ϖ : F) ^ S.a) = algebraMap F E S.ϖ ^ A) (n v : ℕ)
    (hv : algebraMap F E S.ϖ ^ v * algebraMap F E 2⁻¹ ∈ L.O) (w y : S.MW) (hw : S.Mv J d Λ w)
    (hy : y ∈ intP S Λ) (hl : algebraMap F E S.ϖ ^ (n + A + 1 + v) • y ∈ lin S J) :
    S.Mv J d Λ (w + algebraMap F E S.ϖ ^ (n + A + 1 + v) • y) := by sorry
