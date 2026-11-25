-- Prove2me | Theorems.Thm_GlobalTheory_Models_maxModel_eq
-- name    : GlobalTheory.Models.maxModel_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:59.854055+00:00
-- url     : https://prove2.me/theorems/5cb55fff-56d0-58a7-a76d-e26e3e5bf6a4
-- title:
--   Models: max Model eq
-- statement:
--   The Models construction uses the max Model eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L275-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L275-L278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}

theorem GlobalTheory.Models.maxModel_eq {F : DFun R n G} {Base : ∀ A : Ob k G, Lats k n A.m → Prop} {A : Ob k G}
    {N : Lats k n A.m} (h : IsModel F Base A N) (hmax : ∀ N', IsModel F Base A N' → ∀ i, N' i ≤ N i) :
    maxModel F Base A = N := by sorry
