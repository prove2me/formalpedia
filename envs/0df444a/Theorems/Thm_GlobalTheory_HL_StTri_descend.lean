-- Prove2me | Theorems.Thm_GlobalTheory_HL_StTri_descend
-- name    : GlobalTheory.HL.StTri.descend
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:26.736471+00:00
-- url     : https://prove2.me/theorems/70c61f39-94ed-5ef0-8648-c19c86eebc04
-- title:
--   St Tri: descend
-- statement:
--   The St Tri construction uses the descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalFrameStabilizerActsUnitriangular.lean#L13-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalFrameStabilizerActsUnitriangular.lean#L13-L39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StTri

theorem GlobalTheory.HL.StTri.descend {E R : Type} [Field E] [CommRing R] [Nontrivial R] (ι : E →+* R) {n m : ℕ}
    (w : Fin m → Fin n → E) (s : Set (Fin m)) (v : Fin n → E)
    (h : (fun i => ι (v i)) ∈ Submodule.span R ((fun a i => ι (w a i)) '' s)) :
    v ∈ Submodule.span E (w '' s) := by sorry
