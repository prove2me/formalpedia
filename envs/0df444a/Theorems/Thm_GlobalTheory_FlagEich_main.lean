-- Prove2me | Theorems.Thm_GlobalTheory_FlagEich_main
-- name    : GlobalTheory.FlagEich.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:32.747741+00:00
-- url     : https://prove2.me/theorems/34d19d04-c954-441b-a06b-fe456ca96f43
-- title:
--   Flag Eich: main
-- statement:
--   The Flag Eich construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L378-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L378-L403

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
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
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler

theorem GlobalTheory.FlagEich.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (g j.castSucc) = 0 ∧ S.h (u i) (gs j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (g i.castSucc) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by sorry
