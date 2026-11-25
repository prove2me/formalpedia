-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolCoef_eabH_eq_fderiv
-- name    : GlobalTheory.CompanionTheory.HolCoef.eabH_eq_fderiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:46.924216+00:00
-- url     : https://prove2.me/theorems/3dd9488a-c5cf-5746-83e0-9dcb4254f4e2
-- title:
--   Hol Coef: eab H eq fderiv
-- statement:
--   The Hol Coef construction uses the eab H eq fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/HasDerivAtExpReal.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/HasDerivAtExpReal.lean#L78-L89

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

theorem GlobalTheory.CompanionTheory.HolCoef.eabH_eq_fderiv (H g : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : DifferentiableAt ℂ f g) : EabH H a b f g = fderiv ℂ f g (g * Matrix.single a b 1) := by sorry
