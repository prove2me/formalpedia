-- Prove2me | Theorems.Thm_GlobalTheory_CrudeValue_nabVal_monomial
-- name    : GlobalTheory.CrudeValue.nabVal_monomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:14.776086+00:00
-- url     : https://prove2.me/theorems/ac923e03-e049-430b-9a24-81da991a7094
-- title:
--   Crude Value: nab Val monomial
-- statement:
--   The Crude Value construction uses the nab Val monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L49-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CrudeValue
variable {k : Type} [CommRing k] {d : ℕ}
variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]

theorem GlobalTheory.CrudeValue.nabVal_monomial (B : FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (e : ι →₀ ℕ) :
    B.nabVal k h w0 q f u (MvPolynomial.monomial e 1) =
      constantCoeff (DmonOf (B.G.mapF (algebraMap R k)) u e
        (f * FB.expS k ((q : k) • B.hL k h w0))) := by sorry
