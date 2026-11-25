-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolCoef_ldV_eq_fderiv
-- name    : GlobalTheory.CompanionTheory.HolCoef.ldV_eq_fderiv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:19.21243+00:00
-- url     : https://prove2.me/theorems/84300b96-5a90-5a90-857d-8a466eac7675
-- title:
--   Hol Coef: ld V eq fderiv
-- statement:
--   The Hol Coef construction uses the ld V eq fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/HasDerivAtExpReal.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/HasDerivAtExpReal.lean#L64-L76

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
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.CompanionTheory.HolCoef.ldV_eq_fderiv {k r : ℕ} (X g : B.Mat k r) (f : B.Mat k r → E)
    (hf : DifferentiableAt ℂ f g) : B.LdV X f g = fderiv ℂ f g (-(X * g)) := by sorry
