-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_repr_coord
-- name    : GlobalTheory.QuadraticZeta.repr_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:13.535732+00:00
-- url     : https://prove2.me/theorems/bf913017-a43e-45a1-824c-1fbe5d156618
-- title:
--   Quadratic Zeta: repr coord
-- statement:
--   The Quadratic Zeta construction uses the repr coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L17-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {R : Type*} [CommRing R]

theorem GlobalTheory.QuadraticZeta.repr_coord (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) (x y : ℤ) :
    b.repr (x + y * b 1) 0 = x ∧ b.repr (x + y * b 1) 1 = y := by sorry
