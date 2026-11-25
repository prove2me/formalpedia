-- Prove2me | Theorems.Thm_GlobalTheory_HL_WitIndep_coords_mem
-- name    : GlobalTheory.HL.WitIndep.coords_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:16.367226+00:00
-- url     : https://prove2.me/theorems/4494dd0a-e0ef-4aa4-ae0c-3436724886c6
-- title:
--   Wit Indep: coords mem
-- statement:
--   The Wit Indep construction uses the coords mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermInvariantsIndependentOfWitnesses.lean#L129-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermInvariantsIndependentOfWitnesses.lean#L129-L158

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem GlobalTheory.HL.WitIndep.coords_mem (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V)
    (hA : S.IsInner g gs A) (n : S.GLV) (c : Fin (r + 1) → E) :
    ∑ i, c i • n (g i) ∈ n • S.stdLat g gs A ↔ ∀ i, c i ∈ L.O := by sorry
