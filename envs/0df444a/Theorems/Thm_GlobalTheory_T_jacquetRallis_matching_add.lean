-- Prove2me | Theorems.Thm_GlobalTheory_T_jacquetRallis_matching_add
-- name    : GlobalTheory.T.jacquetRallis_matching_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:30.322366+00:00
-- url     : https://prove2.me/theorems/90d93d6e-5ae5-5906-ad1b-941d94c1ad27
-- title:
--   T: jacquet Rallis matching add
-- statement:
--   The T construction uses the jacquet Rallis matching add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisMatchingAddStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisMatchingAddStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAdd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAddStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.jacquetRallis_matching_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by sorry
