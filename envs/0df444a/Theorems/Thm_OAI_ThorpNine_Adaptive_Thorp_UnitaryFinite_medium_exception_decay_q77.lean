-- Prove2me | Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_UnitaryFinite_medium_exception_decay_q77
-- name    : OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.medium_exception_decay_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:55:33.118597+00:00
-- url     : https://prove2.me/theorems/8fc1db1e-7261-4dba-903b-0716065a9547
-- title:
--   OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.medium_exception_decay_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.medium_exception_decay` of [lean/OAI/Probability/ThorpRouting/Adaptive/InsertionPerm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Adaptive/InsertionPerm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite`, with `open scoped BigOperators Classical`, `open DimensionEstimates`):
--
--   ```lean
--   theorem medium_exception_decay_q77 (L r : ℕ) (h ε t : ℝ) (ht : 0≤t)
--       (hcount : t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000)
--       (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
--       (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
--       (hd : h*(2:ℝ)^(L+r)≤Real.log (Module.finrank ℂ V))
--       (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V))
--       (hM : ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
--         ∀ e : Card (L+r) ↪ Card (L+r),
--           modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r))) :
--       ‖sampleOperator ρ (palindromePerm (L+r))‖≤
--         Real.exp (Real.log (blockGap L)*ε*(2:ℝ)^r)+Real.exp (-h*(2:ℝ)^(L+r)/16000)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThorpNine.Adaptive.Thorp.BenesCoins`, `OAI.ThorpNine.Adaptive.Thorp.blockGap`, `OAI.ThorpNine.Adaptive.Thorp.modifiedRowMoment`, `OAI.ThorpNine.Adaptive.Thorp.palindromePerm` and `OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.IsUnitary` (definitions bundle `OAIQ077T000` of this split); `OAI.ThorpNine.Adaptive.Thorp.Card`, `OAI.ThorpNine.Adaptive.Thorp.SwitchIndex`, `OAI.ThorpNine.Adaptive.Thorp.instDecidableEqSwitchIndex`, `OAI.ThorpNine.Adaptive.Thorp.instFintypeSwitchIndex` and `OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.sampleOperator` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proof of `OAI.ThorpNine.Adaptive.Thorp.Specht.exponential_dimension_spectral_q77` of this split imports it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Adaptive/InsertionPerm.lean (declaration OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.medium_exception_decay)

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem medium_exception_decay_q77 (L r : ℕ) (h ε t : ℝ) (ht : 0≤t)
    (hcount : t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000)
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hd : h*(2:ℝ)^(L+r)≤Real.log (Module.finrank ℂ V))
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V))
    (hM : ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
      ∀ e : Card (L+r) ↪ Card (L+r),
        modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r))) :
    ‖sampleOperator ρ (palindromePerm (L+r))‖≤
      Real.exp (Real.log (blockGap L)*ε*(2:ℝ)^r)+Real.exp (-h*(2:ℝ)^(L+r)/16000) := by
  sorry

end Thorp.UnitaryFinite

end ThorpNine.Adaptive

end OAI
end
