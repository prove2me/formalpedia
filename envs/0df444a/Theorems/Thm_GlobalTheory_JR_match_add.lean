-- Prove2me | Theorems.Thm_GlobalTheory_JR_match_add
-- name    : GlobalTheory.JR.match_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:27.343161+00:00
-- url     : https://prove2.me/theorems/99d8f367-5491-47b9-89d1-3899dbe17dd2
-- title:
--   JR: match add
-- statement:
--   The JR construction uses the match add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisMatchingAdd.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisMatchingAdd.lean#L12-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.match_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by sorry
