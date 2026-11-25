-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_bq_eq
-- name    : GlobalTheory.CompanionTheory.BmuIwa.bq_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:21:44.225467+00:00
-- url     : https://prove2.me/theorems/bfaad696-aa05-46ee-b382-a64147f97009
-- title:
--   Bmu Iwa: bq eq
-- statement:
--   The Bmu Iwa construction uses the bq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwasawaDecomposition.lean#L115-L120

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuIwa
open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder

theorem GlobalTheory.CompanionTheory.BmuIwa.bq_eq (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    bq k r i = if i.val ≤ r ∨ r + k ≤ i.val then 2 * (i.val : ℤ) - (2 * r + k) else 0 := by sorry
