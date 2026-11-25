-- Prove2me | Theorems.Thm_GlobalTheory_T_globalFrameStabilizer_acts_unitriangular
-- name    : GlobalTheory.T.globalFrameStabilizer_acts_unitriangular
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:59:32.281834+00:00
-- url     : https://prove2.me/theorems/4cab6312-6de5-40da-b3b6-293587b1b073
-- title:
--   T: global Frame Stabilizer acts unitriangular
-- statement:
--   The T construction uses the global Frame Stabilizer acts unitriangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalFrameStabilizerActsUnitriangularStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalFrameStabilizerActsUnitriangularStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangularStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.globalFrameStabilizer_acts_unitriangular : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by sorry
