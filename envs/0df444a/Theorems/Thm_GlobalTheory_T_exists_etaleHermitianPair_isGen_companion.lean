-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_etaleHermitianPair_isGen_companion
-- name    : GlobalTheory.T.exists_etaleHermitianPair_isGen_companion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:36.883097+00:00
-- url     : https://prove2.me/theorems/f96a0e21-6537-5f3c-8d52-50c1da956dd1
-- title:
--   T: exists etale Hermitian Pair is Gen companion
-- statement:
--   The T construction uses the exists etale Hermitian Pair is Gen companion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleHermitianPairIsGenCompanionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleHermitianPairIsGenCompanionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleHermitianPairIsGenCompanion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleHermitianPairIsGenCompanionStatement
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

theorem GlobalTheory.T.exists_etaleHermitianPair_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F), (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by sorry
