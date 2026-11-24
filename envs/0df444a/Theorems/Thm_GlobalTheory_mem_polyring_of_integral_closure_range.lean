-- Prove2me | Theorems.Thm_GlobalTheory_mem_polyring_of_integral_closure_range
-- name    : GlobalTheory.mem_polyring_of_integral_closure_range
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:19.825862+00:00
-- url     : https://prove2.me/theorems/472ba241-b351-4b38-bb3b-4a237d07568c
-- title:
--   Global Theory: mem polyring of integral closure range
-- statement:
--   The Global Theory construction uses the mem polyring of integral closure range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPolyringOfIntegralClosureRange.lean#L6-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPolyringOfIntegralClosureRange.lean#L6-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPolyringOfIntegralClosureRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.mem_polyring_of_integral_closure_range : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by sorry
