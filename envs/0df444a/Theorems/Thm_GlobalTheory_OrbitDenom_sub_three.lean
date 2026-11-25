-- Prove2me | Theorems.Thm_GlobalTheory_OrbitDenom_sub_three
-- name    : GlobalTheory.OrbitDenom.sub_three
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:24.985392+00:00
-- url     : https://prove2.me/theorems/9aba44ff-52b5-4de9-b87e-75c0e5bbe1d1
-- title:
--   Orbit Denom: sub three
-- statement:
--   The Orbit Denom construction uses the sub three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L80-L85

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

theorem GlobalTheory.OrbitDenom.sub_three {n l : ℕ} (h : l ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hB : ∀ a k : Fin n, k < a → B a k = 0) :
    (A * W * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * W.submatrix (Fin.castLE h) (Fin.castLE h) *
        B.submatrix (Fin.castLE h) (Fin.castLE h) := by sorry
