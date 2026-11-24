-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unram_tri_mul_affPt
-- name    : GlobalTheory.RootEx.Unram.tri_mul_affPt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:30:26.779856+00:00
-- url     : https://prove2.me/theorems/4d270d55-043f-4125-bdec-3b44e0cffdce
-- title:
--   Unram: tri mul aff Pt
-- statement:
--   The Unram construction uses the tri mul aff Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L65-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n'] [DecidableEq n']

theorem GlobalTheory.RootEx.Unram.tri_mul_affPt {p : ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hM : M.BlockTriangular (lev p))
    (x₀ : Matrix n n' k) (e) (i : Fin c) (r : n ⊕ Fin c) (hr : i.val + 1 ≤ lev p r) :
    (M * affPt (c := c) p x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) r (Sum.inr i.castSucc) = M r (Sum.inr i) := by sorry
