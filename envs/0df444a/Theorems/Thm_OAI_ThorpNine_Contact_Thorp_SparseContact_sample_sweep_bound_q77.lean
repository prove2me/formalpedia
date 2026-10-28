-- Prove2me | Theorems.Thm_OAI_ThorpNine_Contact_Thorp_SparseContact_sample_sweep_bound_q77
-- name    : OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:56:49.073787+00:00
-- url     : https://prove2.me/theorems/313399b0-85c6-424c-826b-f50af76c6244
-- title:
--   OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound` of [lean/OAI/Probability/ThorpRouting/Contact/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Contact/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Contact.Thorp.SparseContact`, with `open scoped BigOperators Classical`):
--
--   ```lean
--   lemma sample_sweep_bound_q77 (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
--       [Representation.IsIrreducible ρ] (hρ : UnitaryFinite.IsUnitary ρ)
--       (x₀ : L ↪ Card d) (w : V) (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ ρ w)
--       (hn : ‖w‖ = 1)
--       (hh : ∀ v, Harmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
--         (UnitaryFinite.tupleAction_transitive x₀) ρ w v))
--       (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
--       (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
--       ‖UnitaryFinite.sampleOperator ρ (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))‖ ≤
--         (2:ℝ)^(Fintype.card L) *
--           Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
--             Real.exp (Real.exp 1*(Fintype.card L)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThorpNine.Contact.Thorp.SparseContact.Harmonic`, `OAI.ThorpNine.Contact.Thorp.UnitaryFinite.IsFixed`, `OAI.ThorpNine.Contact.Thorp.UnitaryFinite.IsUnitary`, `OAI.ThorpNine.Contact.Thorp.UnitaryFinite.normalizedCoefficient`, `OAI.ThorpNine.Contact.Thorp.UnitaryFinite.tupleAction` and `OAI.ThorpNine.Contact.Thorp.UnitaryFinite.tupleAction_transitive` (definitions bundle `OAIQ077T001` of this split); `OAI.ThorpNine.Contact.Thorp.Card`, `OAI.ThorpNine.Contact.Thorp.SwitchIndex`, `OAI.ThorpNine.Contact.Thorp.butterflyPerm`, `OAI.ThorpNine.Contact.Thorp.decodeButterfly`, `OAI.ThorpNine.Contact.Thorp.instDecidableEqSwitchIndex`, `OAI.ThorpNine.Contact.Thorp.instFintypeSwitchIndex` and `OAI.ThorpNine.Contact.Thorp.UnitaryFinite.sampleOperator` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proof of `OAI.ThorpNine.Contact.Thorp.SparseContact.uniform_sparse_contact_q77` of this split imports it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Contact/Main.lean (declaration OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound)

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp.SparseContact
open scoped BigOperators Classical

section Generic
variable {L V : Type*} [Fintype L] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma sample_sweep_bound_q77 (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    [Representation.IsIrreducible ρ] (hρ : UnitaryFinite.IsUnitary ρ)
    (x₀ : L ↪ Card d) (w : V) (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ ρ w)
    (hn : ‖w‖ = 1)
    (hh : ∀ v, Harmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) ρ w v))
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖UnitaryFinite.sampleOperator ρ (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))‖ ≤
      (2:ℝ)^(Fintype.card L) *
        Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))) := by
  sorry

end Generic

end Thorp.SparseContact

end ThorpNine.Contact

end OAI
end
