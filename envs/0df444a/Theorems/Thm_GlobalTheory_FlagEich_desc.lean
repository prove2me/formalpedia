-- Prove2me | Theorems.Thm_GlobalTheory_FlagEich_desc
-- name    : GlobalTheory.FlagEich.desc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:46.730807+00:00
-- url     : https://prove2.me/theorems/e2c81620-d4f5-4baa-9342-88be31ae00b2
-- title:
--   Flag Eich: desc
-- statement:
--   The Flag Eich construction uses the desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L339-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L339-L374

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

theorem GlobalTheory.FlagEich.desc {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0)
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0) :
    ∀ d m : ℕ, m + d = r → ∀ n ∈ S.Nof g,
      (∀ a : Fin r, (a : ℕ) < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) →
      ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV),
        (∀ i, (∀ j, j ≤ i → hf L S.Hm (u i) (g j.castSucc) = 0 ∧ hf L S.Hm (u i) (gs j) = 0) ∧
          s i + L.cj (s i) = hf L S.Hm (u i) (u i) ∧
          ∀ v, e i v = eich L S.Hm (g i.castSucc) (u i) (s i) v) ∧
        (∀ i : Fin r, (i : ℕ) < m → e i = 1) ∧ n = (List.ofFn e).prod := by sorry
