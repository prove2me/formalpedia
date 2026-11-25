-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_pr_val
-- name    : GlobalTheory.CompanionTheory.BesselLevi.pr_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:42:02.246036+00:00
-- url     : https://prove2.me/theorems/0e13863a-0c46-4590-a6a7-d0c77a715564
-- title:
--   Bessel Levi: pr val
-- statement:
--   The Bessel Levi construction uses the pr val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LeviDecomposition.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LeviDecomposition.lean#L17-L31

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

theorem GlobalTheory.CompanionTheory.BesselLevi.pr_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ((i.val ≤ r ∨ r + k ≤ i.val) ∧ (pr k r i).val + i.val = 2 * r + k) ∨
      (r < i.val ∧ i.val < r + k ∧ (pr k r i).val = i.val) := by sorry
