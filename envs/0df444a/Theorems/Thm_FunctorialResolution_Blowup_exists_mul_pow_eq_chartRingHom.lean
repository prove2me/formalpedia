-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_exists_mul_pow_eq_chartRingHom
-- name    : FunctorialResolution.Blowup.exists_mul_pow_eq_chartRingHom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:10:18.000854+00:00
-- url     : https://prove2.me/theorems/c708b9f6-57d4-496c-b96e-c61158427ee9
-- title:
--   Blowup: exists mul pow eq chart Ring Hom
-- statement:
--   The Blowup construction uses the exists mul pow eq chart Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L72-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L72-L109

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u

theorem FunctorialResolution.Blowup.exists_mul_pow_eq_chartRingHom {R : Type u} [CommRing R] (I : Ideal R) (a : ↥I)
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    ∃ (n : ℕ) (r : R), z * chartRingHom I a (a : R) ^ n = chartRingHom I a r := by sorry
