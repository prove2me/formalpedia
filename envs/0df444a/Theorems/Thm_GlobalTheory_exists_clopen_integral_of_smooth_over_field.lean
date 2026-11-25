-- Prove2me | Theorems.Thm_GlobalTheory_exists_clopen_integral_of_smooth_over_field
-- name    : GlobalTheory.exists_clopen_integral_of_smooth_over_field
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:44.353831+00:00
-- url     : https://prove2.me/theorems/e4dd005b-8397-4512-b91b-c8ac28507b0b
-- title:
--   Global Theory: exists clopen integral of smooth over field
-- statement:
--   The Global Theory construction uses the exists clopen integral of smooth over field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsClopenIntegralOfSmoothOverField.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsClopenIntegralOfSmoothOverField.lean#L10-L27

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsClopenIntegralOfSmoothOverField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory

theorem GlobalTheory.exists_clopen_integral_of_smooth_over_field :
    ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z,
      ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧
        z ∈ Set.range j := by sorry
