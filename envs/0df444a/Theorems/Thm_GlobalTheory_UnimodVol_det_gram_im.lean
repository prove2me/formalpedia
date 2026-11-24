-- Prove2me | Theorems.Thm_GlobalTheory_UnimodVol_det_gram_im
-- name    : GlobalTheory.UnimodVol.det_gram_im
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:38.188912+00:00
-- url     : https://prove2.me/theorems/1c9593c5-153a-4e40-85b1-479b82015855
-- title:
--   Unimod Vol: det gram im
-- statement:
--   The Unimod Vol construction uses the det gram im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/VolumeFundamentalDomainStdRealBasis.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/VolumeFundamentalDomainStdRealBasis.lean#L40-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_VolumeFundamentalDomainStdRealBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UnimodVol

theorem GlobalTheory.UnimodVol.det_gram_im {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (v : (Σ _ : Fin g, Fin 2) → Fin g → ℂ) :
    (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im).det =
      ((stdRealBasis g).det v) ^ 2 * ‖Hm.det‖ ^ 2 := by sorry
