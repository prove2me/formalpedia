-- Prove2me | Theorems.Thm_GlobalTheory_exists_sum_eigen_split_of_resolvent
-- name    : GlobalTheory.exists_sum_eigen_split_of_resolvent
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:07:22.789245+00:00
-- url     : https://prove2.me/theorems/73cde024-722d-5818-aa47-010911657cfb
-- title:
--   Global Theory: exists sum eigen split of resolvent
-- statement:
--   The Global Theory construction uses the exists sum eigen split of resolvent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsEigenSplitOfResolventIdentity.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsEigenSplitOfResolventIdentity.lean#L9-L22

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AevalNegEqZeroOfResolventIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumEigenvectorsOfAevalProdLinearEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEigenSplitOfResolventIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory

theorem GlobalTheory.exists_sum_eigen_split_of_resolvent : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by sorry
