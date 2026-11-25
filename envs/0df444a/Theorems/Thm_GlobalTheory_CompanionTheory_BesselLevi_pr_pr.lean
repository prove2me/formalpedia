-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_pr_pr
-- name    : GlobalTheory.CompanionTheory.BesselLevi.pr_pr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:22:48.77891+00:00
-- url     : https://prove2.me/theorems/212368e6-5d97-5581-987c-15074c25abad
-- title:
--   Bessel Levi: pr pr
-- statement:
--   The Bessel Levi construction uses the pr pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LeviDecomposition.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LeviDecomposition.lean#L33-L37

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselLevi

theorem GlobalTheory.CompanionTheory.BesselLevi.pr_pr (k r : ℕ) (i : Fin (2 * r + k + 1)) : pr k r (pr k r i) = i := by sorry
