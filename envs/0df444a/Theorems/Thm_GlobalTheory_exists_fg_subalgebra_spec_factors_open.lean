-- Prove2me | Theorems.Thm_GlobalTheory_exists_fg_subalgebra_spec_factors_open
-- name    : GlobalTheory.exists_fg_subalgebra_spec_factors_open
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:09.893798+00:00
-- url     : https://prove2.me/theorems/b0af2634-282d-465f-ae74-227f9db5f6d9
-- title:
--   Global Theory: exists fg subalgebra spec factors open
-- statement:
--   The Global Theory construction uses the exists fg subalgebra spec factors open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFgSubalgebraSpecFactorThroughOpen.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFgSubalgebraSpecFactorThroughOpen.lean#L9-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFgSubalgebraSpecFactorThroughOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.exists_fg_subalgebra_spec_factors_open (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (R : Subalgebra o Ω) (hR : R.FG) (V : (Sp R).Opens) (hV : (V : Set (Sp R)).Nonempty) :
    ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧
      ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by sorry
