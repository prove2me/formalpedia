-- Prove2me | Theorems.Thm_GlobalTheory_LogLinear_formalGroup_log_endomorphism_linear
-- name    : GlobalTheory.LogLinear.formalGroup_log_endomorphism_linear
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:03:27.364014+00:00
-- url     : https://prove2.me/theorems/8ec28a4e-6256-4530-a467-be6cce4d25d2
-- title:
--   Log Linear: formal Group log endomorphism linear
-- statement:
--   The Log Linear construction uses the formal Group log endomorphism linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalGroupLogEndomorphismLinear.lean#L64-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalGroupLogEndomorphismLinear.lean#L64-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalGroupLogEndomorphismLinear
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.LogLinear
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.LogLinear.formalGroup_log_endomorphism_linear :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ α : Pt k 1 d),
      (∀ i, MvPowerSeries.constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
      comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
      (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ i, comp1 ℓ α i = ∑ j, MvPowerSeries.C (dLin α i j) * ℓ j := by sorry
