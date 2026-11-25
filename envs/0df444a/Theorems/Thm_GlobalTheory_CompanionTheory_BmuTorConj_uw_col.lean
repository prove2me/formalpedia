-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_uw_col
-- name    : GlobalTheory.CompanionTheory.BmuTorConj.uw_col
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:41:25.954667+00:00
-- url     : https://prove2.me/theorems/c0890ab0-7641-4ae7-937c-46ef635cbd5a
-- title:
--   Bmu Tor Conj: uw col
-- statement:
--   The Bmu Tor Conj construction uses the uw col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusConjugacy.lean#L57-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusConjugacy.lean#L57-L73

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugacy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuTorConj

theorem GlobalTheory.CompanionTheory.BmuTorConj.uw_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val)
    (i : Fin (2 * r + k + 1)) : h i p = if i = p then 1 else 0 := by sorry
