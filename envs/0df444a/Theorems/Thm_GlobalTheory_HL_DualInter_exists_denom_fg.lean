-- Prove2me | Theorems.Thm_GlobalTheory_HL_DualInter_exists_denom_fg
-- name    : GlobalTheory.HL.DualInter.exists_denom_fg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:39:46.828071+00:00
-- url     : https://prove2.me/theorems/5faf1bf9-60bd-4732-ae41-3dbb90936115
-- title:
--   Dual Inter: exists denom fg
-- statement:
--   The Dual Inter construction uses the exists denom fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L82-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L82-L100

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm}
variable [IsNonarchimedeanLocalField F]

theorem GlobalTheory.HL.DualInter.exists_denom_fg {Λ : Submodule L.O (Fin n → E)} (hΛ : Λ.FG) (y : Fin n → E) :
    ∃ d ∈ L.O, IsUnit d ∧ ∀ x ∈ Λ, d * hf L Hm x y ∈ L.O := by sorry
