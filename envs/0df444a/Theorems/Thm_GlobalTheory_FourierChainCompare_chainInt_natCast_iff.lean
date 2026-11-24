-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_chainInt_natCast_iff
-- name    : GlobalTheory.FourierChainCompare.chainInt_natCast_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:54:57.445373+00:00
-- url     : https://prove2.me/theorems/173ab81a-e4de-466e-9d4b-bbdecb478d3b
-- title:
--   Fourier Chain Compare: chain Int nat Cast iff
-- statement:
--   The Fourier Chain Compare construction uses the chain Int nat Cast iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L342-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L342-L348

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.FourierChainCompare.chainInt_natCast_iff {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (P : MvPolynomial ι R) (k n : ℕ) (f : PS R 1 d) :
    (constantCoeff (DpolyOf G.F u P (ev ![mulN G n] f)) =
        (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)) ↔
      constantCoeff (DpolyOf G.F u P (ev ![A.act (((n : ℤ) : O))] f)) =
        (((n : ℤ) : R)) ^ k * constantCoeff (DpolyOf G.F u P f) := by sorry
