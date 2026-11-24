-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_lead_unit
-- name    : GlobalTheory.FrameBasic.lead_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:22.813822+00:00
-- url     : https://prove2.me/theorems/7f4f4984-0cad-409f-9892-af62d40e56b2
-- title:
--   Frame Basic: lead unit
-- statement:
--   The Frame Basic construction uses the lead unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L112-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L112-L133

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

theorem GlobalTheory.FrameBasic.lead_unit {n : ℕ} (w : Pt E n) (ε : Fin n → E) (hε : ∀ b, IsUnit (ε b))
    {m : ℕ} (hm : m ≤ n) :
    ((Matrix.of fun a b => w.mat a b * ε b).submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 →
    IsUnit ((Matrix.of fun a b => w.mat a b * ε b).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by sorry
