-- Prove2me | Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_primitive
-- name    : GlobalTheory.HL.OrthCompl.exists_primitive
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:35:47.634186+00:00
-- url     : https://prove2.me/theorems/27d727bd-8b57-57d2-8d9c-cf1abad1fde8
-- title:
--   Orth Compl: exists primitive
-- statement:
--   The Orth Compl construction uses the exists primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L96-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L96-L138

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
variable {o E : Type*} [CommRing o] [IsLocalRing o] [CommRing E]
omit [IsLocalRing o]

theorem GlobalTheory.HL.OrthCompl.exists_primitive [IsArtinianRing E] [IsReduced E] (S : Subring E) [IsPrincipalIdealRing S]
    (hid : ∀ e : E, e * e = e → e ∈ S) {y0 y1 y2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) :
    ∃ d : E, ∃ b0 ∈ S, ∃ b1 ∈ S, ∃ b2 ∈ S, ∃ r0 ∈ S, ∃ r1 ∈ S, ∃ r2 ∈ S,
      y0 = d * b0 ∧ y1 = d * b1 ∧ y2 = d * b2 ∧ b0 * r0 + b1 * r1 + b2 * r2 = 1 := by sorry
