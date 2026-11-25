-- Prove2me | Theorems.Thm_GlobalTheory_FlagEich_step
-- name    : GlobalTheory.FlagEich.step
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:34.830281+00:00
-- url     : https://prove2.me/theorems/04b6d60f-528f-4f3b-b506-1472d61ed134
-- title:
--   Flag Eich: step
-- statement:
--   The Flag Eich construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L259-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L259-L330

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.FlagEich.step {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0)
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (m : Fin r)
    (hfix : ∀ a : Fin r, a < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) :
    ∃ (u : S.V) (s : E) (e : S.GLV),
      ((∀ j : Fin r, j ≤ m → hf L S.Hm u (g j.castSucc) = 0 ∧ hf L S.Hm u (gs j) = 0) ∧
        s + L.cj s = hf L S.Hm u u ∧ ∀ v, e v = eich L S.Hm (g m.castSucc) u s v) ∧
      e ∈ S.Nof g ∧ ∀ a : Fin r, a ≤ m → (e⁻¹ * n) (g a.castSucc) = g a.castSucc ∧
        (e⁻¹ * n) (gs a) = gs a := by sorry
