-- Prove2me | Theorems.Thm_GlobalTheory_local_height_scaling
-- name    : GlobalTheory.local_height_scaling
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:08:59.958668+00:00
-- url     : https://prove2.me/theorems/0aa5abd1-aa7e-4ea1-94ab-9fd91e25b816
-- title:
--   Global Theory: local height scaling
-- statement:
--   The Global Theory construction uses the local height scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalHeightScaling.lean#L47-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalHeightScaling.lean#L47-L135

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramSumElimSmulSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalModelModulusPropertiesOnUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalHeightScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory

theorem GlobalTheory.local_height_scaling : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (P : LocNG.FPair H r), P.Gv ≠ 0 → ∀ (e : F), e ≠ 0 → ∀ (G : E) (d : ℕ → E), P.Gv = algebraMap F E (e⁻¹ ^ (2 * r * (r + 1))) * G → (∀ l ∈ P.ends, P.Dm l = algebraMap F E (e⁻¹ ^ (l * (2 * r + 1 - l))) * d l) → (P.PrimeTo → P.Hp = 1) ∧ P.Hp = M.modK (algebraMap F E (LocNG.theta M)) ^ ((2 * r + 1 : ℝ) / 2) * M.modK (algebraMap F E e) ^ ((r * (r + 1) + ∑ l ∈ P.ends, l * (2 * r + 1 - l) : ℕ) : ℝ) * M.modK G ^ (-(1 / 2 : ℝ)) * ∏ l ∈ P.ends, (M.modK (d l))⁻¹ := by sorry
