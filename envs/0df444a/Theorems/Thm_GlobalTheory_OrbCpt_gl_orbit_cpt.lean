-- Prove2me | Theorems.Thm_GlobalTheory_OrbCpt_gl_orbit_cpt
-- name    : GlobalTheory.OrbCpt.gl_orbit_cpt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:54.485929+00:00
-- url     : https://prove2.me/theorems/ebc0a480-1b40-4841-9491-8ab5711bdee7
-- title:
--   Orb Cpt: gl orbit cpt
-- statement:
--   The Orb Cpt construction uses the gl orbit cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L100-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L100-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}

theorem GlobalTheory.OrbCpt.gl_orbit_cpt (A₀ : Matrix (Fin r) (Fin r) k) (hs : A₀.charpoly.Separable)
    (Z : Set (Matrix (Fin r) (Fin r) k)) (hZ : IsCompact Z) :
    ∃ C : Set (GL (Fin r) k), IsCompact C ∧ ∀ g : GL (Fin r) k,
      (g : Matrix (Fin r) (Fin r) k) * A₀ * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) ∈ Z →
      ∃ c ∈ C, ∃ t : GL (Fin r) k,
        (t : Matrix (Fin r) (Fin r) k) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) k) ∧ g = c * t := by sorry
