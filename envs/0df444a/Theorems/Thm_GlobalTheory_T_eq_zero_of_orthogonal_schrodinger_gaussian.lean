-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_orthogonal_schrodinger_gaussian
-- name    : GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:22.820274+00:00
-- url     : https://prove2.me/theorems/c153b7f9-39d8-4c18-bd9c-abeeac54c61d
-- title:
--   T: eq zero of orthogonal schrodinger gaussian
-- statement:
--   The T construction uses the eq zero of orthogonal schrodinger gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroOfOrthogonalSchrodingerGaussianStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroOfOrthogonalSchrodingerGaussianStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroOfOrthogonalSchrodingerGaussian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroOfOrthogonalSchrodingerGaussianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l), (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume) (k.toLp 2 volume) = 0) → k = 0 := by sorry
