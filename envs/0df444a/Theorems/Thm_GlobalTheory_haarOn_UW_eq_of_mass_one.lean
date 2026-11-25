-- Prove2me | Theorems.Thm_GlobalTheory_haarOn_UW_eq_of_mass_one
-- name    : GlobalTheory.haarOn_UW_eq_of_mass_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:44.230925+00:00
-- url     : https://prove2.me/theorems/7ed99d59-b1ab-54ba-9510-e20f30d7d3f8
-- title:
--   Global Theory: haar On UW eq of mass one
-- statement:
--   The Global Theory construction uses the haar On UW eq of mass one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryMeasureDatumProductMeasureEqOfSameVectors.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryMeasureDatumProductMeasureEqOfSameVectors.lean#L12-L19

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryMeasureDatumProductMeasureEqOfSameVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q MeasureTheory
open GlobalTheory

theorem GlobalTheory.haarOn_UW_eq_of_mass_one {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μ ν : Measure (Mt k r))
    (hμ : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) (hν : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) ν)
    (h1 : μ Set.univ = 1) (h2 : ν Set.univ = 1) : ν = μ := by sorry
