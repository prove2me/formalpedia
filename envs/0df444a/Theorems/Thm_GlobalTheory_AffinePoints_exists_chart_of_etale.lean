-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_chart_of_etale
-- name    : GlobalTheory.AffinePoints.exists_chart_of_etale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:04.75431+00:00
-- url     : https://prove2.me/theorems/60a0f950-600e-4fdc-b88f-69a51cd9f2d9
-- title:
--   Affine Points: exists chart of etale
-- statement:
--   The Affine Points construction uses the exists chart of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOpenPartialHomeomorphAnalytic.lean#L79-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOpenPartialHomeomorphAnalytic.lean#L79-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

theorem GlobalTheory.AffinePoints.exists_chart_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g ∧
      ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target := by sorry
