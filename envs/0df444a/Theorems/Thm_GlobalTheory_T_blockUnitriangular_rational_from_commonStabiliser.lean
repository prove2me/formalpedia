-- Prove2me | Theorems.Thm_GlobalTheory_T_blockUnitriangular_rational_from_commonStabiliser
-- name    : GlobalTheory.T.blockUnitriangular_rational_from_commonStabiliser
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:44.873797+00:00
-- url     : https://prove2.me/theorems/cba32fb2-284a-56c3-ac1e-c0ebdce94a4a
-- title:
--   T: block Unitriangular rational from common Stabiliser
-- statement:
--   The T construction uses the block Unitriangular rational from common Stabiliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliserStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliserStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliserStatement
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

theorem GlobalTheory.T.blockUnitriangular_rational_from_commonStabiliser : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → t i j = if i = j then 1 else 0) → ∃ g ∈ G.St, ∀ j, g (G.f j) = ∑ i, t i j • G.f i := by sorry
