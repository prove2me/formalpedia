-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_hpk_row
-- name    : GlobalTheory.CompanionTheory.BmuTorConj.hpk_row
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:22:35.417099+00:00
-- url     : https://prove2.me/theorems/b0822ece-f0e2-4315-b822-5c213336c43d
-- title:
--   Bmu Tor Conj: hpk row
-- statement:
--   The Bmu Tor Conj construction uses the hpk row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusConjugacy.lean#L39-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusConjugacy.lean#L39-L55

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

theorem GlobalTheory.CompanionTheory.BmuTorConj.hpk_row (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hpq : p.val + q.val = 2 * r + k)
    (h : p.val < r ∨ q.val < r) (j : Fin (2 * r + k + 1)) :
    Hpk k r p j = if j = q then 1 else 0 := by sorry
