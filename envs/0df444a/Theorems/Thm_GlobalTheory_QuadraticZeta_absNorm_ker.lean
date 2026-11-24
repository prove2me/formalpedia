-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_ker
-- name    : GlobalTheory.QuadraticZeta.absNorm_ker
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:07.373594+00:00
-- url     : https://prove2.me/theorems/9c85445d-5f0d-4f45-81e1-1c4b854faf16
-- title:
--   Quadratic Zeta: abs Norm ker
-- statement:
--   The Quadratic Zeta construction uses the abs Norm ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L165-L168

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

theorem GlobalTheory.QuadraticZeta.absNorm_ker {p : ℕ} (φ : 𝓞 K →+* ZMod p) : Ideal.absNorm (RingHom.ker φ) = p := by sorry
