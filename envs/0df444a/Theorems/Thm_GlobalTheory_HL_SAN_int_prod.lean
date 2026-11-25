-- Prove2me | Theorems.Thm_GlobalTheory_HL_SAN_int_prod
-- name    : GlobalTheory.HL.SAN.int_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:23.535565+00:00
-- url     : https://prove2.me/theorems/8e6e36a5-bf20-4554-bc9b-99307b3f7134
-- title:
--   SAN: int prod
-- statement:
--   The SAN construction uses the int prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemCoord.lean#L99-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemCoord.lean#L99-L115

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.SAN.int_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (m : ℕ) (X u : Fin m → Fin N → E) (s : Fin m → E)
    (e : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, u i j ∈ L.O) →
    (∀ i, s i ∈ L.O) → (∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v) →
    ∀ x : Fin N → E, (∀ j, x j ∈ L.O) → ∀ j, (List.ofFn e).prod x j ∈ L.O := by sorry
