-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedHensel_taylor_bound
-- name    : GlobalTheory.UnramifiedHensel.taylor_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:32.266288+00:00
-- url     : https://prove2.me/theorems/c4451b89-147d-40db-a7dd-2061ac58284c
-- title:
--   Unramified Hensel: taylor bound
-- statement:
--   The Unramified Hensel construction uses the taylor bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L100-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L100-L138

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

theorem GlobalTheory.UnramifiedHensel.taylor_bound [Fintype ι] [DecidableEq ι] (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1)
    (x y : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hxy : ∀ i, ‖y i - x i‖ ≤ r) (G : MvPolynomial ι R) :
    ‖eval₂ c y G - eval₂ c x G - ∑ j, eval₂ c x (pderiv j G) * (y j - x j)‖ ≤ r * r := by sorry
