-- Prove2me | Theorems.Thm_GlobalTheory_LeadingMinors_det_X_mem_supported
-- name    : GlobalTheory.LeadingMinors.det_X_mem_supported
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:19.327694+00:00
-- url     : https://prove2.me/theorems/3eaef755-ac7e-4418-92f8-edb5be331a80
-- title:
--   Leading Minors: det X mem supported
-- statement:
--   The Leading Minors construction uses the det X mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CoeffProdLeadingMinors.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CoeffProdLeadingMinors.lean#L26-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.LeadingMinors
open MvPowerSeries

theorem GlobalTheory.LeadingMinors.det_X_mem_supported {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) (S : Set σ) (hS : ∀ a i, v a i ∈ S) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det ∈
      MvPolynomial.supported k S := by sorry
