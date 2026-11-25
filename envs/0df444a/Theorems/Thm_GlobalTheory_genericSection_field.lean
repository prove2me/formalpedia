-- Prove2me | Theorems.Thm_GlobalTheory_genericSection_field
-- name    : GlobalTheory.genericSection_field
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:34.282026+00:00
-- url     : https://prove2.me/theorems/eb5d2fc6-75ef-431e-9ff6-2a8345d4ea99
-- title:
--   Global Theory: generic Section field
-- statement:
--   The Global Theory construction uses the generic Section field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GenericSectionInjectiveOfAxH.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GenericSectionInjectiveOfAxH.lean#L19-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GenericSectionInjectiveOfAxH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT

theorem GlobalTheory.genericSection_field {k F : Type} [Field k] [CharZero k] [Field F] [Algebra k F] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → F) (hfg : (⊤ : IntermediateField k F).FG)
    (htr : Algebra.trdeg k F = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent F fun a => KaehlerDifferential.D k F (x (J a))) :
    AlgebraicIndependent k (sImg (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x))) (OmS F D N) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x)))
        (OmS F D N) := by sorry
