-- Prove2me | Theorems.Thm_GlobalTheory_HL_Glue_mem_span_single_iff
-- name    : GlobalTheory.HL.Glue.mem_span_single_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:31:44.90492+00:00
-- url     : https://prove2.me/theorems/7d5cc8ed-576c-55ca-9026-6b9834226ad8
-- title:
--   Glue: mem span single iff
-- statement:
--   The Glue construction uses the mem span single iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanSingleIff.lean#L19-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanSingleIff.lean#L19-L39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem GlobalTheory.HL.Glue.mem_span_single_iff {R : Type} [CommRing R] (O : Subring R) (n : ℕ)
    (v : Fin n → R) :
    v ∈ Submodule.span O (Set.range fun i => (Pi.single i 1 : Fin n → R)) ↔ ∀ i, v i ∈ O := by sorry
