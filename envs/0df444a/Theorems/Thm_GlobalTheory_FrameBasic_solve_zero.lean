-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_solve_zero
-- name    : GlobalTheory.FrameBasic.solve_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:30.701287+00:00
-- url     : https://prove2.me/theorems/25c757c2-bf6e-4dc2-93be-eb1a0192afae
-- title:
--   Frame Basic: solve zero
-- statement:
--   The Frame Basic construction uses the solve zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L164-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L164-L180

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]

theorem GlobalTheory.FrameBasic.solve_zero {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det)
    (hG : IsUnit (Z.det * Z'.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z'.submatrix Fin.castSucc Fin.castSucc).det)))
    (α β : Fin (r + 1) → E) (h1 : Z.mulVec β = Pi.single (Fin.last r) (T * α (Fin.last r)))
    (h2 : Z'.mulVec α = Pi.single (Fin.last r) (T' * β (Fin.last r))) : α = 0 ∧ β = 0 := by sorry
