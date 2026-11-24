-- Prove2me | Theorems.Thm_GlobalTheory_OrbCpt_isCompact_units_image
-- name    : GlobalTheory.OrbCpt.isCompact_units_image
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:48.848676+00:00
-- url     : https://prove2.me/theorems/1e516ded-1ae0-4c4d-a687-3f70110bdfbd
-- title:
--   Orb Cpt: is Compact units image
-- statement:
--   The Orb Cpt construction uses the is Compact units image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L80-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L80-L98

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

theorem GlobalTheory.OrbCpt.isCompact_units_image {X : Type} [TopologicalSpace X] {P : Set X} (hP : IsCompact P)
    {f : X → Matrix (Fin r) (Fin r) k} (hf : Continuous f) (hdet : ∀ x ∈ P, (f x).det ≠ 0) :
    ∃ C : Set (GL (Fin r) k), IsCompact C ∧
      ∀ x ∈ P, ∃ c ∈ C, (c : Matrix (Fin r) (Fin r) k) = f x := by sorry
