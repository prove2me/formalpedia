-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedHensel_mem_of_gradient
-- name    : GlobalTheory.UnramifiedHensel.mem_of_gradient
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:45.111364+00:00
-- url     : https://prove2.me/theorems/2afaf070-826f-4a96-9406-e3c96713c222
-- title:
--   Unramified Hensel: mem of gradient
-- statement:
--   The Unramified Hensel construction uses the mem of gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L140-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L140-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel
variable {K : Type} [NormedField K] [IsUltrametricDist K] {R ι : Type} [CommRing R]

theorem GlobalTheory.UnramifiedHensel.mem_of_gradient [Fintype ι] [DecidableEq ι] (W : Subring K) (hW : IsClosed (W : Set K))
    (hc : ∀ w ∈ W, ‖w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (h0 : ∀ i, ∃ w ∈ W, ‖x i - w‖ < 1) (G : ι → MvPolynomial ι W)
    (hG : ∀ i, eval₂ W.subtype x (G i) = 0)
    (hd : ∀ i j, ‖(if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖ < 1) (i : ι) :
    x i ∈ W := by sorry
