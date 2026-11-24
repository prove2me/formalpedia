-- Prove2me | Theorems.Thm_GlobalTheory_unitary_transitive_of_norm
-- name    : GlobalTheory.unitary_transitive_of_norm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:22.679895+00:00
-- url     : https://prove2.me/theorems/dec26e81-364c-4080-a84d-5d8ba458c7b8
-- title:
--   Global Theory: unitary transitive of norm
-- statement:
--   The Global Theory construction uses the unitary transitive of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L83-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L83-L93

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.unitary_transitive_of_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (u v : Fin r → E), star u ⬝ᵥ u = star v ⬝ᵥ v →
    star u ⬝ᵥ u ≠ 0 → ∃ g : Matrix.unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by sorry
