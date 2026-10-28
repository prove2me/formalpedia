-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_LinearGrowth_StrongFullSpan_virtually_comm_range_bs
-- name    : OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:33:17.976842+00:00
-- url     : https://prove2.me/theorems/ea6bcf20-d904-4a30-83e8-dcc46a1d745b
-- title:
--   OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range` of [lean/OAI/Probability/CriticalPercolation/LinearGroups/StrongAbstractSpan.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/LinearGroups/StrongAbstractSpan.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.LinearGrowth`, with `open Set Function Module`, `open scoped Classical`):
--
--   ```lean
--   lemma StrongFullSpan.virtually_comm_range_bs (ρ : G →* (V ≃ₗ[K] V))
--       (hρ : StrongFullSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) :
--       ∃ H : Subgroup G, H.FiniteIndex ∧
--         ∀ x y : (ρ.comp H.subtype).range, x*y=y*x
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.LinearGrowth.StrongFullSpan` and `OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs` and `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/LinearGroups/StrongAbstractSpan.lean (declaration OAI.CriticalPercolation.LinearGrowth.StrongFullSpan.virtually_comm_range)

import Mathlib
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type} [Field K] [CharZero K] [Countable K] [IsAlgClosed K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
variable [Group G] [DecidableEq G]
variable {degree : ℕ}

lemma StrongFullSpan.virtually_comm_range_bs (ρ : G →* (V ≃ₗ[K] V))
    (hρ : StrongFullSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∀ x y : (ρ.comp H.subtype).range, x*y=y*x := by
  sorry

end CriticalPercolation.LinearGrowth
end
end

end OAI
end
