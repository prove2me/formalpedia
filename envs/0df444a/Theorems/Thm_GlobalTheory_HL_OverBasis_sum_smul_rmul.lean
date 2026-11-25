-- Prove2me | Theorems.Thm_GlobalTheory_HL_OverBasis_sum_smul_rmul
-- name    : GlobalTheory.HL.OverBasis.sum_smul_rmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:57.000319+00:00
-- url     : https://prove2.me/theorems/28272d69-552d-4646-a40b-4c7d6cb54832
-- title:
--   Over Basis: sum smul rmul
-- statement:
--   The Over Basis construction uses the sum smul rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LinearIndependentOfGram.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LinearIndependentOfGram.lean#L39-L43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LinearIndependentOfGram
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OverBasis
open Matrix GlobalTheory.HL.SelfDual
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
omit [TopologicalSpace E]

theorem GlobalTheory.HL.OverBasis.sum_smul_rmul {n m : ℕ} (y : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (c : Fin m → E) : ∑ j, c j • rmul y B j = ∑ i, (B *ᵥ c) i • y i := by sorry
