-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_diag_mem
-- name    : GlobalTheory.CompanionTheory.BesselLevi.diag_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:46:45.247705+00:00
-- url     : https://prove2.me/theorems/1e46b2c3-8d6c-4663-804c-16f079afc7bc
-- title:
--   Bessel Levi: diag mem
-- statement:
--   The Bessel Levi construction uses the diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LeviDecomposition.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LeviDecomposition.lean#L79-L90

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

theorem GlobalTheory.CompanionTheory.BesselLevi.diag_mem (k r : ℕ) (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, conj (d i) * d (pr k r i) = 1) :
    Matrix.diagonal d ∈ UH (Hq k r) := by sorry
