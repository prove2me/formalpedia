-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_hasAdj_qdet
-- name    : GlobalTheory.CompanionTheory.CapelliAdj.hasAdj_qdet
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:40.345548+00:00
-- url     : https://prove2.me/theorems/e12d1f92-f0ea-4e45-8cbf-aeb7c5b540f5
-- title:
--   Capelli Adj: has Adj qdet
-- statement:
--   The Capelli Adj construction uses the has Adj qdet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L87-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L87-L102

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

theorem GlobalTheory.CompanionTheory.CapelliAdj.hasAdj_qdet {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) :
    HasAdj B (qdet X v)
      (MulOpposite.unop (qdet (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) v))) := by sorry
