-- Prove2me | Theorems.Thm_GlobalTheory_FiniteQuotientComap_finite_quotient_comap
-- name    : GlobalTheory.FiniteQuotientComap.finite_quotient_comap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:32.745675+00:00
-- url     : https://prove2.me/theorems/f00a9773-c11f-4056-b18e-3c9a5dbde719
-- title:
--   Finite Quotient Comap: finite quotient comap
-- statement:
--   The Finite Quotient Comap construction uses the finite quotient comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteQuotientComap.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteQuotientComap.lean#L43-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteQuotientComap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.FiniteQuotientComap

theorem GlobalTheory.FiniteQuotientComap.finite_quotient_comap {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L₀ L : Submodule (𝓞 E) (Fin n → E)) (h₀ : L₀.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by sorry
