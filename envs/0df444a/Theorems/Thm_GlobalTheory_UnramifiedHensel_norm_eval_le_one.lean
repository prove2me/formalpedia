-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedHensel_norm_eval_le_one
-- name    : GlobalTheory.UnramifiedHensel.norm_eval_le_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:23.023641+00:00
-- url     : https://prove2.me/theorems/ad3e5abb-d85e-425d-97ab-97fbb63b6429
-- title:
--   Unramified Hensel: norm eval le one
-- statement:
--   The Unramified Hensel construction uses the norm eval le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L86-L94

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

theorem GlobalTheory.UnramifiedHensel.norm_eval_le_one (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (G : MvPolynomial ι R) : ‖eval₂ c x G‖ ≤ 1 := by sorry
