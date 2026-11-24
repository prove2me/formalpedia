-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_inv_mul_affPt_apply
-- name    : GlobalTheory.RootEx.Supp.inv_mul_affPt_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:28:26.562994+00:00
-- url     : https://prove2.me/theorems/1293d917-0bde-45a8-b7dd-05c3270efa9e
-- title:
--   Supp: inv mul aff Pt apply
-- statement:
--   The Supp construction uses the inv mul aff Pt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L242-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L242-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp

theorem GlobalTheory.RootEx.Supp.inv_mul_affPt_apply {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} {b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hb : b.BlockTriangular (lev p)) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n ⊕ Fin c) (j : Fin c)
    (h : lev p r = lev p (Sum.inr j : n ⊕ Fin c)) :
    (b * affPt p x₀ e) r (Sum.inr j.castSucc) = b r (Sum.inr j) := by sorry
