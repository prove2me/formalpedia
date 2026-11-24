-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordExist_hf_basis
-- name    : GlobalTheory.HL.CoordExist.hf_basis
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:59:05.932186+00:00
-- url     : https://prove2.me/theorems/0ba3bfa6-3288-40c7-a8f2-fbab0ef7e307
-- title:
--   Coord Exist: hf basis
-- statement:
--   The Coord Exist construction uses the hf basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NotField.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NotField.lean#L46-L48

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordExist
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem GlobalTheory.HL.CoordExist.hf_basis (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) (x y : V) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) (b.equivFun x) (b.equivFun y) = H.h x y := by sorry
