-- Prove2me | Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_Truncation_card_univ_mul_sum_compl_le
-- name    : MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_univ_mul_sum_compl_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:15:42.033209+00:00
-- url     : https://prove2.me/theorems/b59863db-f7d4-4a5d-97df-4ef8bbe66ca4
-- title:
--   Partition-total form of the pairwise bound. If S = Lᶜ, the paper's r · ∑_{Small} o ≤ |Small| · ∑ o follows from card_mul_sum_small_le after splitting ∑ x, f x = ∑_L f +…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.TruncationCombinatorics` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Combinatorial core of the `r > d` truncation branch. Helper lemmas for the `r > d` branch of `lem:projective-low-rank-sum` (`references/ldt-paper/orthonormalization.tex:559-658`). Given a finite family of overlap values `f : α → ℝ` (with `α` the pair index set `{(a, i)}` carrying `r = |α|` entries) and a chosen `Large ⊂ α` of size `d < r` such that every `Small = Lᶜ` entry has overlap `≤` every `Large` entry, the paper derives * `|Large| * ∑_{Small} f ≤ |Small| * ∑_{Large} f` (pairwise double-counting), * `r * ∑_{Small} f ≤ |Small| * ∑_{α} f` (partition bound). We then combine…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Partition-total form of the pairwise bound.**
--
--   If `S = Lᶜ`, the paper's `r · ∑_{Small} o ≤ |Small| · ∑ o` follows from
--   `card_mul_sum_small_le` after splitting `∑ x, f x = ∑_L f + ∑_{Lᶜ} f`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open scoped BigOperators
--
--   theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_univ_mul_sum_compl_le {α : Type*} [Fintype α] [DecidableEq α]
--       (L : Finset α) {f : α → ℝ}
--       (hf : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l) :
--       (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) ≤
--         (Lᶜ.card : ℝ) * (∑ x, f x)
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_univ_mul_sum_compl_le` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean`, lines 133–160. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean#L133-L160

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_univ_mul_sum_compl_le {α : Type*} [Fintype α] [DecidableEq α]
    (L : Finset α) {f : α → ℝ}
    (hf : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l) :
    (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) ≤
      (Lᶜ.card : ℝ) * (∑ x, f x) := by sorry
