-- Prove2me | Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_Truncation_sum_small_le_four_sqrt
-- name    : MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:15:42.802325+00:00
-- url     : https://prove2.me/theorems/94270074-a115-4a37-a553-0efc619d3d9a
-- title:
--   Small-overlap sum bound. Assuming the paper's inputs: * L.card = d with d < |α|, * |α| ≤ (1 + 2√ζ) · d, * every Small = Lᶜ entry has value at most every Large = L…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.TruncationCombinatorics` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Combinatorial core of the `r > d` truncation branch. Helper lemmas for the `r > d` branch of `lem:projective-low-rank-sum` (`references/ldt-paper/orthonormalization.tex:559-658`). Given a finite family of overlap values `f : α → ℝ` (with `α` the pair index set `{(a, i)}` carrying `r = |α|` entries) and a chosen `Large ⊂ α` of size `d < r` such that every `Small = Lᶜ` entry has overlap `≤` every `Large` entry, the paper derives * `|Large| * ∑_{Small} f ≤ |Small| * ∑_{Large} f` (pairwise double-counting), * `r * ∑_{Small} f ≤ |Small| * ∑_{α} f` (partition bound). We then combine…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Small-overlap sum bound.**
--
--   Assuming the paper's inputs:
--
--   * `L.card = d` with `d < |α|`,
--   * `|α| ≤ (1 + 2√ζ) · d`,
--   * every `Small = Lᶜ` entry has value at most every `Large = L` entry,
--   * `∑ x, f x ≤ 1 + 2√ζ`,
--   * `0 ≤ ζ ≤ 1/4`,
--
--   this yields `∑_{Small} f ≤ 4√ζ`, matching `eq:small-overlaps` in the paper. The
--   Lean statement is slightly stronger than the paper's: it does not need `f ≥ 0`,
--   since the ordering hypothesis and partition-total estimate already suffice.
--   See `docs/paper-gaps/truncation-combinatorics-f-nonneg.tex`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open scoped BigOperators
--
--   theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt {α : Type*} [Fintype α] [DecidableEq α]
--       (L : Finset α)
--       {f : α → ℝ}
--       {d : ℕ} {ζ : ℝ}
--       (hL_card : L.card = d)
--       (hcard_gt : d < Fintype.card α)
--       (hr_bound : (Fintype.card α : ℝ) ≤ (1 + 2 * Real.sqrt ζ) * d)
--       (hf_ordering : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l)
--       (htotal : (∑ x, f x) ≤ 1 + 2 * Real.sqrt ζ)
--       (hζ_nonneg : 0 ≤ ζ)
--       (hζ_le : ζ ≤ 1 / 4) :
--       (∑ s ∈ (Lᶜ : Finset α), f s) ≤ 4 * Real.sqrt ζ
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean`, lines 162–252. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean#L162-L252

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt {α : Type*} [Fintype α] [DecidableEq α]
    (L : Finset α)
    {f : α → ℝ}
    {d : ℕ} {ζ : ℝ}
    (hL_card : L.card = d)
    (hcard_gt : d < Fintype.card α)
    (hr_bound : (Fintype.card α : ℝ) ≤ (1 + 2 * Real.sqrt ζ) * d)
    (hf_ordering : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l)
    (htotal : (∑ x, f x) ≤ 1 + 2 * Real.sqrt ζ)
    (hζ_nonneg : 0 ≤ ζ)
    (hζ_le : ζ ≤ 1 / 4) :
    (∑ s ∈ (Lᶜ : Finset α), f s) ≤ 4 * Real.sqrt ζ := by sorry
