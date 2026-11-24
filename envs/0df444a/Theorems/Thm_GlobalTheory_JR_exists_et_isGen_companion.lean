-- Prove2me | Theorems.Thm_GlobalTheory_JR_exists_et_isGen_companion
-- name    : GlobalTheory.JR.exists_et_isGen_companion
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:38:34.374834+00:00
-- url     : https://prove2.me/theorems/d5935a84-b944-402c-b533-6d154870c494
-- title:
--   JR: exists et is Gen companion
-- statement:
--   The JR construction uses the exists et is Gen companion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleHermitianPairIsGenCompanion.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleHermitianPairIsGenCompanion.lean#L55-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleHermitianPairIsGenCompanion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.exists_et_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F),
    (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by sorry
