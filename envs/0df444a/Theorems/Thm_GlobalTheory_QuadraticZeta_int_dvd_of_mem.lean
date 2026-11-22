-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_int_dvd_of_mem
-- name    : GlobalTheory.QuadraticZeta.int_dvd_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:34:28.104159+00:00
-- url     : https://prove2.me/theorems/17fdba53-7f17-41b2-a2c7-4a5998244b9b
-- title:
--   Quadratic Zeta: int dvd of mem
-- statement:
--   The Quadratic Zeta construction uses the int dvd of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L160-L163

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
variable {K : Type*} [Field K] [NumberField K]

theorem GlobalTheory.QuadraticZeta.int_dvd_of_mem {p : ℕ} {P : Ideal (𝓞 K)} (hP : P.under ℤ = .span {(p : ℤ)}) (x : ℤ) :
    (x : 𝓞 K) ∈ P ↔ (p : ℤ) ∣ x := by sorry
