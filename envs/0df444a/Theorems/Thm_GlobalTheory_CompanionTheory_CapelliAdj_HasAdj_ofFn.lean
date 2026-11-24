-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_ofFn
-- name    : GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.ofFn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:23.799314+00:00
-- url     : https://prove2.me/theorems/436987c5-f1c0-41ed-a212-47eb1b0c59a8
-- title:
--   Has Adj: of Fn
-- statement:
--   The Has Adj construction uses the of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L32-L44

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

theorem GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.ofFn {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ V) (g : Fin t → (Module.End ℂ V)ᵐᵒᵖ),
      (∀ k, HasAdj B (f k) (MulOpposite.unop (g k))) →
      HasAdj B (List.ofFn f).prod (MulOpposite.unop (List.ofFn g).prod) := by sorry
