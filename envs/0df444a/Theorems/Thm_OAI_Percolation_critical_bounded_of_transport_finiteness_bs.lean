-- Prove2me | Theorems.Thm_OAI_Percolation_critical_bounded_of_transport_finiteness_bs
-- name    : OAI.Percolation.critical_bounded_of_transport_finiteness_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:41:06.776432+00:00
-- url     : https://prove2.me/theorems/ce08e5f9-b095-46ac-9ff9-4aa6cc169ff0
-- title:
--   OAI.Percolation.critical_bounded_of_transport_finiteness_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.critical_bounded_of_transport_finiteness` of [lean/OAI/Probability/UnimodularPercolation/Criticality/Operator.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Criticality/Operator.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem critical_bounded_of_transport_finiteness_bs [Infinite V]
--       (G : BondGraph V E) (hG : Function.Injective G)
--       (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
--       {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
--       (htr : RootTransport root weight (vertexAut G))
--       (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
--       (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
--       (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
--       OperatorBounded G (pc G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.RootTransport` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.vertexAut` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.OperatorBounded`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.cluster`, `OAI.Percolation.hV`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proofs of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.full_application_conditional_bs`, `OAI.Percolation.BenjaminiSchramm.full_application_gap_bs`, `OAI.Percolation.BenjaminiSchramm.full_main` and `OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Criticality/Operator.lean (declaration OAI.Percolation.critical_bounded_of_transport_finiteness)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Filter
open scoped Topology

universe u v
variable {V : Type u} {E : Type v}

theorem critical_bounded_of_transport_finiteness_bs [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
    OperatorBounded G (pc G) := by
  sorry

end Percolation

end OAI
end
