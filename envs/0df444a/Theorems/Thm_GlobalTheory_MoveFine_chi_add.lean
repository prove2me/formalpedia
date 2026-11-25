-- Prove2me | Theorems.Thm_GlobalTheory_MoveFine_chi_add
-- name    : GlobalTheory.MoveFine.chi_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:42:20.047829+00:00
-- url     : https://prove2.me/theorems/902ab256-99bd-4bcd-b2f1-fb95f48ab15d
-- title:
--   Move Fine: chi add
-- statement:
--   The Move Fine construction uses the chi add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsFineSubgroupMovesAtLattice.lean#L438-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsFineSubgroupMovesAtLattice.lean#L438-L474

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

theorem GlobalTheory.MoveFine.chi_add (j : Fin r) {d : S.Datum} {Λ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (A : ℕ)
    (hA : algebraMap F E ((S.ϖ : F) ^ S.a) = algebraMap F E S.ϖ ^ A) (n : ℕ) (w y : S.MW)
    (hw : S.Mv (j + 1) d Λ w) (hy : y ∈ intP S Λ) (hl : algebraMap F E S.ϖ ^ (n + A + 1) • y ∈ lin S (j + 1)) :
    S.chiM j d Λ (w + algebraMap F E S.ϖ ^ (n + A + 1) • y).1 (w + algebraMap F E S.ϖ ^ (n + A + 1) • y).2.1 =
      S.chiM j d Λ w.1 w.2.1 := by sorry
