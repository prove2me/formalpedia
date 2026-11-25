-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolCoef_coef_one
-- name    : GlobalTheory.CompanionTheory.HolCoef.coef_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:58.344321+00:00
-- url     : https://prove2.me/theorems/e35dcd9a-257a-4af5-947a-787a35c6c13f
-- title:
--   Hol Coef: coef one
-- statement:
--   The Hol Coef construction uses the coef one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/HasDerivAtExpReal.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/HasDerivAtExpReal.lean#L35-L42

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_ExpEntry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_HasDerivAtExpReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolCoef
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.CompanionTheory.HolCoef.coef_one (p N : ℕ) : coef p N 1 = 1 := by sorry
