-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_exists_chart_affineOpen_mem_nonZeroDivisors
-- name    : FunctorialResolution.Blowup.exists_chart_affineOpen_mem_nonZeroDivisors
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:59.839973+00:00
-- url     : https://prove2.me/theorems/ce763b4f-d3c8-4bbe-8b45-02f24e10d2b5
-- title:
--   Blowup: exists chart affine Open mem non Zero Divisors
-- statement:
--   The Blowup construction uses the exists chart affine Open mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L410-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L410-L466

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

theorem FunctorialResolution.Blowup.exists_chart_affineOpen_mem_nonZeroDivisors {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (h : W ⟶ affineBlowup I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (w : ↥W) :
    ∃ (a : ↥I) (V : W.affineOpens), w ∈ (V : W.Opens) ∧
      (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) ∧
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R) ∈
        nonZeroDivisors ↥Γ(W, (V : W.Opens)) := by sorry
