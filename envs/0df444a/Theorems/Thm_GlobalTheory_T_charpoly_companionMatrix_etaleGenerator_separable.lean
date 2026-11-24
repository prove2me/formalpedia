-- Prove2me | Theorems.Thm_GlobalTheory_T_charpoly_companionMatrix_etaleGenerator_separable
-- name    : GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:43.403795+00:00
-- url     : https://prove2.me/theorems/d9a9ad15-cf51-405d-8280-1bc6fb04e89f
-- title:
--   T: charpoly companion Matrix etale Generator separable
-- statement:
--   The T construction uses the charpoly companion Matrix etale Generator separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyCompanionMatrixEtaleGeneratorSeparableStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyCompanionMatrixEtaleGeneratorSeparableStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyCompanionMatrixEtaleGeneratorSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyCompanionMatrixEtaleGeneratorSeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → (companion p).charpoly.Separable := by sorry
