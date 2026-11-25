-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_inv_sqrt_two_mul_self_bis
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.inv_sqrt_two_mul_self_bis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:35:21.058165+00:00
-- url     : https://prove2.me/theorems/63467285-d87f-5864-87f8-07160ed23f76
-- title:
--   Bmu Adapt: inv sqrt two mul self bis
-- statement:
--   The Bmu Adapt construction uses the inv sqrt two mul self bis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L129-L132

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuAdapt

theorem GlobalTheory.CompanionTheory.BmuAdapt.inv_sqrt_two_mul_self_bis : s2 * s2 = 1 / 2 := by sorry
