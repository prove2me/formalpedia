-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_etaleInvolutiveAlgebraSplitting_smaller
-- name    : GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:16.431614+00:00
-- url     : https://prove2.me/theorems/dfd890c3-4b3a-4c53-bfe7-c15e7a324939
-- title:
--   T: exists etale Involutive Algebra Splitting smaller
-- statement:
--   The T construction uses the exists etale Involutive Algebra Splitting smaller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleInvolutiveAlgebraSplittingSmallerStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleInvolutiveAlgebraSplittingSmallerStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmallerStatement
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

theorem GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K → ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧ Module.finrank F A₂.K < Module.finrank F A.K := by sorry
