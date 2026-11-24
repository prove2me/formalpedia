-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_ncard_dvd
-- name    : GlobalTheory.QuadraticZeta.ncard_dvd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:38.265585+00:00
-- url     : https://prove2.me/theorems/d3e31872-6f60-4978-b30e-eb51c36bbee1
-- title:
--   Quadratic Zeta: ncard dvd
-- statement:
--   The Quadratic Zeta construction uses the ncard dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L138-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L138-L158

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

theorem GlobalTheory.QuadraticZeta.ncard_dvd {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (k : ℕ) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = k ∧ J ∣ I}.ncard
      = if Ideal.absNorm J ∣ k then idealCount K (k / Ideal.absNorm J) else 0 := by sorry
