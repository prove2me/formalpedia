-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_sum
-- name    : GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:19.970462+00:00
-- url     : https://prove2.me/theorems/a7264daf-adc2-4c9a-b9ed-b207863ae0d0
-- title:
--   Has Adj: sum
-- statement:
--   The Has Adj construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L76-L85

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAdj
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.sum {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {ι : Type*} (s : Finset ι)
    (f g : ι → Module.End ℂ V) (h : ∀ i ∈ s, HasAdj B (f i) (g i)) :
    HasAdj B (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by sorry
