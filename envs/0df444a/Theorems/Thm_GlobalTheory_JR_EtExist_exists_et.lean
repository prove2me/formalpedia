-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtExist_exists_et
-- name    : GlobalTheory.JR.EtExist.exists_et
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:50.011799+00:00
-- url     : https://prove2.me/theorems/19e7de0c-1ab9-47af-a066-969be0cd6239
-- title:
--   Et Exist: exists et
-- statement:
--   The Et Exist construction uses the exists et property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactModuleTopology.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactModuleTopology.lean#L109-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactModuleTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtExist
variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (K : Type) [CommRing K] [Algebra F K]

theorem GlobalTheory.JR.EtExist.exists_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [GlobalTheory.JR.Unram F E],
    (∃ A : GlobalTheory.JR.Et F E, IsField A.K ∧ IsField A.L ∧ Module.finrank F A.K = 1) ∧
    ∀ (r : ℕ) (p : Fin r → F),
      (Polynomial.X ^ r + ∑ i, Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) : Polynomial F).Separable →
      ∃ (A : GlobalTheory.JR.Et F E) (τ : A.K), A.IsGen τ p := by sorry
