-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_charpoly_companion_separable
-- name    : GlobalTheory.JR.LinDesc.charpoly_companion_separable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:33:07.444826+00:00
-- url     : https://prove2.me/theorems/f412777f-6c95-4d71-9e5c-da4b88279425
-- title:
--   Lin Desc: charpoly companion separable
-- statement:
--   The Lin Desc construction uses the charpoly companion separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyCompanionMatrixEtaleGeneratorSeparable.lean#L6-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyCompanionMatrixEtaleGeneratorSeparable.lean#L6-L47

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyCompanionMatrixEtaleGeneratorSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc

theorem GlobalTheory.JR.LinDesc.charpoly_companion_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F),
    A.IsGen τ p → (companion p).charpoly.Separable := by sorry
