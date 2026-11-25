-- Prove2me | Theorems.Thm_GlobalTheory_OrbitDenom_adj_mem
-- name    : GlobalTheory.OrbitDenom.adj_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:51.8168+00:00
-- url     : https://prove2.me/theorems/8298b8c3-b263-510b-9e77-7d3115f505f4
-- title:
--   Orbit Denom: adj mem
-- statement:
--   The Orbit Denom construction uses the adj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L53-L62

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
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
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]

theorem GlobalTheory.OrbitDenom.adj_mem (O : Subring E) {l : ℕ} (M : Matrix (Fin l) (Fin l) E) (hM : ∀ a b, M a b ∈ O)
    (a b : Fin l) : M.adjugate a b ∈ O := by sorry
