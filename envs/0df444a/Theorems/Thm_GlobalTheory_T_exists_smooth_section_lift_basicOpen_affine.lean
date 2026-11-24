-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_smooth_section_lift_basicOpen_affine
-- name    : GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:38:27.265128+00:00
-- url     : https://prove2.me/theorems/e3427cb6-3379-4594-8be9-eac72d88aa30
-- title:
--   T: exists smooth section lift basic Open affine
-- statement:
--   The T construction uses the exists smooth section lift basic Open affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffineStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffineStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffine
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffineStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V := by sorry
