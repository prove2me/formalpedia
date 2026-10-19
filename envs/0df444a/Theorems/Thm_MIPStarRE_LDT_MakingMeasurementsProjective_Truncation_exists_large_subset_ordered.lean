-- Prove2me | Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_Truncation_exists_large_subset_ordered
-- name    : MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:15:14.745475+00:00
-- url     : https://prove2.me/theorems/5b31295e-4065-4578-bc6b-3cb2d69d493f
-- title:
--   Choose d elements with the largest values of f, breaking ties arbitrarily
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.TruncationCombinatorics` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Combinatorial core of the `r > d` truncation branch. Helper lemmas for the `r > d` branch of `lem:projective-low-rank-sum` (`references/ldt-paper/orthonormalization.tex:559-658`). Given a finite family of overlap values `f : α → ℝ` (with `α` the pair index set `{(a, i)}` carrying `r = |α|` entries) and a chosen `Large ⊂ α` of size `d < r` such that every `Small = Lᶜ` entry has overlap `≤` every `Large` entry, the paper derives * `|Large| * ∑_{Small} f ≤ |Small| * ∑_{Large} f` (pairwise double-counting), * `r * ∑_{Small} f ≤ |Small| * ∑_{α} f` (partition bound). We then combine…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   Choose `d` elements with the largest values of `f`, breaking ties
--   arbitrarily. The resulting `Large` set has the paper's ordering property:
--   every element outside `Large` has value at most every element of `Large`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open scoped BigOperators
--
--   theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered {α : Type*} [Fintype α] [DecidableEq α]
--       (f : α → ℝ) {d : ℕ} (hd : d ≤ Fintype.card α) :
--       ∃ L : Finset α, L.card = d ∧
--         ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean`, lines 55–104. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean#L55-L104

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {d : ℕ} (hd : d ≤ Fintype.card α) :
    ∃ L : Finset α, L.card = d ∧
      ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l := by sorry
