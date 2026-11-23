-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtExist_exists_isGen
-- name    : GlobalTheory.JR.EtExist.exists_isGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:33.518626+00:00
-- url     : https://prove2.me/theorems/38ca503e-56aa-4889-bec3-8daa7aad4011
-- title:
--   Et Exist: exists is Gen
-- statement:
--   The Et Exist construction uses the exists is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactModuleTopology.lean#L78-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactModuleTopology.lean#L78-L107

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

theorem GlobalTheory.JR.EtExist.exists_isGen [Unram F E] (r : ℕ) (p : Fin r → F)
    (hs : (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]).Separable) : ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by sorry
